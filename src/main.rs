//  WebPeerShare
//  Server for an HTML-based P2P file sharing page
//  Copyright (C) 2021  Matthew Weeks
//
//  This program is free software: you can redistribute it and/or modify
//  it under the terms of the GNU Affero General Public License as
//  published by the Free Software Foundation, either version 3 of the
//  License, or (at your option) any later version.
//
//  This program is distributed in the hope that it will be useful,
//  but WITHOUT ANY WARRANTY; without even the implied warranty of
//  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//  GNU Affero General Public License for more details.
//
//  You should have received a copy of the GNU Affero General Public License
//  along with this program.  If not, see <https://www.gnu.org/licenses/>.
use std::net::{TcpStream, TcpListener, SocketAddr};
use std::io::*;
use std::sync::{Arc, Mutex};
use std::collections::BTreeMap;
type State = BTreeMap<u128, BTreeMap<u32, TcpStream>>;

static WS_BINARY: u8 = 2;
static WS_EOF: u8 = 8;
static WS_PING: u8 = 9;
static WS_PONG: u8 = 10;

static CODE_FULL_LIST: &[u8; 1] = b"\x01";
static CODE_CLIENT_EXIT: &[u8; 1] = b"\x02";
static CODE_CLIENT_BROADCAST: &[u8; 1] = b"\x06";
static CODE_CLIENT_BROADCASTED: &[u8; 1] = b"\x09";
static CODE_CLIENT_ANNOUNCE: &[u8; 1] = b"\x0c";
static CODE_CLIENT_FWD_NOW: &[u8; 1] = b"\x0d";

//reads bytes if not read yet to ensure there's at least len bytes in the vec
fn check_len(s: &mut TcpStream, buf: &mut smallvec::SmallVec::<[u8; 2048]>, min: usize) -> Result<()> {
    let len = buf.len();
    if min > len { // if necessary get more bytes
        buf.resize(min, 0); //grow buffer (may not actually allocate)
        s.read_exact(&mut buf[len..min])?; //read more bytes
    }
    Ok(())
}

//receives a websocket message. Must fit inside buf, with headers.
fn ws_recv<'a>(stream: &mut TcpStream, buf: &'a mut smallvec::SmallVec::<[u8; 2048]>, offsb: &mut usize) -> Result<&'a mut [u8]> {
    for i in 0..(buf.len() - *offsb) { //if there are leftover bytes from a previous message,
        buf[i] = buf[i + *offsb]; //memmove them down to the beginning of the buffer and continue
    }
    buf.truncate(buf.len() - *offsb); //then resize down
    *offsb = 0;
    if buf.len() == 0 {
        buf.resize(buf.capacity(), 0);
        let readb = stream.read(&mut buf[..])?;
        buf.truncate(readb); //read in whatever's available and truncate to there
    };
    check_len(stream, buf, 2)?; //but make sure it's at least 2 bytes, then parse length
    let (leng, offs) = if buf[1] & 0x7F == 127 {
        check_len(stream, buf, 10)?; //make sure we can fit all this
        let lenbytes = [buf[2], buf[3], buf[4], buf[5], buf[6], buf[7], buf[8], buf[9]];
        (u64::from_be_bytes(lenbytes) as usize, 10) // More than 64k?
    } else if buf[1] & 0x7F == 126 {
        check_len(stream, buf, 4)?;
        (buf[2] as usize * 256 + buf[3] as usize, 4)
    } else {
        ((buf[1] & 0x7F) as usize, 2)
    };
    *offsb = offs;
    let mut mask = [0; 4];
    let masked = buf[1] & 0x80 != 0;
    if masked {
        check_len(stream, buf, *offsb + 4)?; //make sure we can fit
        (&mut mask[..]).copy_from_slice(&buf[*offsb..*offsb + 4]);
        *offsb += 4;
    }
    check_len(stream, buf, *offsb + leng)?; //read the rest of the data if needed
    if masked {
        for i in 0..leng {
            buf[*offsb + i] ^= mask[i % 4]; //demask
        }
    }
    let code = buf[0] & 0xF;
    let startoffs = *offsb;
    *offsb += leng; // now we've handled this much
    if code == WS_PING { //ping
        ws_send(stream, &buf[startoffs..startoffs + leng], WS_PONG)?; //answer the ping
        return ws_recv(stream, buf, offsb) //recurse and try again
    } else if code == WS_PONG {
        return ws_recv(stream, buf, offsb) //recurse and try again
    } else if code == WS_EOF {
        return Err(Error::from(ErrorKind::UnexpectedEof))
    }
    Ok(&mut buf[startoffs..startoffs + leng]) //return the read buf
}

//Sends a websocket message.
fn ws_send(stream: &mut TcpStream, sendable: &[u8], code: u8) -> Result<()> {
    let mut buf = [0; 2048];
    buf[0] = 0x80 | code;
    let (len_byte, offset) = if sendable.len() < 126 {
        (sendable.len() as u8, 2)
    } else if sendable.len() < (1 << 16) {
        (&mut buf[2..4]).copy_from_slice(&(sendable.len() as u16).to_be_bytes()[..]);
        (126, 4)
    } else {
        (&mut buf[2..10]).copy_from_slice(&(sendable.len() as u64).to_be_bytes()[..]);
        (127, 10)
    };
    buf[1] = len_byte;
    let chunk_len = sendable.len().min(buf.len() - offset);
    (&mut buf[offset..offset + chunk_len]).copy_from_slice(&sendable[..chunk_len]);
    stream.write_all(&buf[..offset + chunk_len])?; //send headers and first chunk
    if sendable.len() > chunk_len {
        stream.write_all(&sendable[chunk_len..])?; //send rest of the sendable
    }
    Ok(())
}

//Replies to an HTTP request for /
fn handle_root(stream: &mut TcpStream) -> Result<()> {
    let mut headers = [0; 1024];
    let mut cur = Cursor::new(&mut headers[..]);
    let mut body = &b"Did not find index.html"[..];
    let found_bod = std::fs::read("index.html").ok();
    if let Some(b) = found_bod.as_ref(){
        body = &b[..];
    }
    write!(cur, "HTTP/1.1 200 OK\r\n\
X-Content-Type-Options: nosniff\r\n\
X-Frame-Options: DENY\r\n\
Cache-Control: no-cache\r\n\
Referrer-Policy: no-referrer\r\n\
Connection: Close\r\n\
Content-Type: text/html\r\n\
Content-Length: {}\r\n\r\n", body.len())?; //normal headers
    let wrotelen = cur.position() as usize;
    stream.write_all(&headers[..wrotelen])?; //Send all the headers as one chunk
    stream.write_all(&body[..]) //Then the body as a second chunk
}

//initializes a websocket connection
fn setup_websocket_server_connection(stream: &mut TcpStream) -> Result<bool> {
    let mut buf = [0; 2048]; //we don't do cookies or anything, should be plenty, but maybe not
    let rlen = stream.read(&mut buf)?;
    let mut data = smallvec::SmallVec::from_buf_and_len(buf, rlen); //read
    while data.windows(4).position(|w| w == b"\r\n\r\n").is_none() {
        let mut anotherbuf = [0; 2048];
        let morebytes = stream.read(&mut anotherbuf)?; // find \r\n\r\n or keep receiving
        data.extend_from_slice(&anotherbuf[..morebytes]);
    }
    let needle = b"Sec-WebSocket-Key: "; //find the header or return root
    let idx = if let Some(i) = data.windows(needle.len()).position(|w| w == needle) { i } else {
        handle_root(stream)?;
        return Ok(false);
    };
    let remaining = &data[idx + needle.len()..]; //find end of header or return error
    let eidx = remaining.windows(2).position(|w| w == b"\r\n").ok_or(Error::from(ErrorKind::NotFound))?;
    let mut sh = sha1::Sha1::from(&remaining[..eidx]); //Now start hashing the header
    sh.update(b"258EAFA5-E914-47DA-95CA-C5AB0DC85B11");//and add the GUID per RFC 6455
    let mut b64shabuf = [0; 28]; //base64 of 20 bytes=28 bytes e.g. mPAaw2+T4L/9lVIs0rTsmXWAShQ=
    base64::encode_config_slice(&sh.digest().bytes(), base64::STANDARD, &mut b64shabuf);
    let mut cur = Cursor::new(&mut buf[..]); //now write your response to a buffer
    cur.write_all(b"HTTP/1.1 101 Switching Protocols\r\n\
Connection: Upgrade\r\n\
Upgrade: websocket\r\n\
Sec-Websocket-Accept: ")?;
    cur.write_all(&b64shabuf)?;
    cur.write_all(b"\r\n\r\n")?;
    let response_len = cur.position() as usize;
    stream.write_all(&buf[..response_len])?;
    Ok(true)
}

//handle a client message
fn do_one(conns: &mut BTreeMap<u32, TcpStream>, buf: &mut [u8]) -> Result<()> {
    if buf.len() > 5 && buf[0] == CODE_CLIENT_FWD_NOW[0]{
        let dest = u32::from_le_bytes([buf[1],buf[2],buf[3],buf[4]]);
        if let Some(other_stream) = conns.get_mut(&dest){
            println!("forwarding {} bytes to {}", buf.len() - 5, dest);  //legit client
            if let Err(e) = ws_send(other_stream, &buf[5..], WS_BINARY) {
                println!("Error forwarding to {}: {}", dest, e);
            }
        }else{
            println!("Couldn't find {} maybe they left", dest);
        }
    } else if buf.len() > 1 && buf[0] == CODE_CLIENT_BROADCAST[0] {
        println!("Broadcasting {} bytes", buf.len());
        buf[0] = CODE_CLIENT_BROADCASTED[0];
        for (_key, other_stream) in conns.iter_mut() {
            ws_send(other_stream, buf, WS_BINARY)?;
        }
    } else if buf.len() == 0 || buf[0] != 0 {
        print!("unknown cmd {} bytes: ", buf.len());
        for b in buf {
            print!("{:02X}", b);
        }
        println!();
    }
    Ok(())
}

//Handles a client connection
fn do_it(mut stream: TcpStream, state: Arc<Mutex<State>>, address: SocketAddr) -> Result<()> {
    stream.set_read_timeout(Some(std::time::Duration::new(60, 0)))?; //1m timeout (PING's every 15s)
    if ! setup_websocket_server_connection(&mut stream)? {
        return Ok(()); //not a websocket
    }
    let mut recvvec = smallvec::SmallVec::new();
    let mut zoneid: u128 = 0;
    let mut offsb = 0;
    if let Ok(r) = ws_recv(&mut stream, &mut recvvec, &mut offsb) {
        if r.len() == 16 {
            zoneid = u128::from_le_bytes([r[0],r[1],r[2],r[3],r[4],r[5],r[6],r[7],r[8],r[9],r[10],
                r[11],r[12],r[13],r[14],r[15]]); //get zone
        }
    } else {
        return Ok(()); //no luck
    }

    let mut rcv_stream = stream.try_clone()?; //another view of the same socket for sending threads
    let mut full_list = smallvec::SmallVec::<[u8; 2048]>::new();
    full_list.write_all(CODE_FULL_LIST)?;
    let mut stat = if let Ok(s) = state.lock() { s } else {
        return Err(Error::from(ErrorKind::InvalidInput)); // shouldn't happen on most platforms
    };
    if let None = stat.get(&zoneid){
        stat.insert(zoneid, Default::default()); //make a new zone if not there
    } //OK FROM THIS POINT ON, we don't want to return err without cleaning up first
    let zone = stat.get_mut(&zoneid).unwrap();
    let mut id = 0;
    while zone.get(&id).is_some() { id+=1; }
    let mut my_addr_announce = smallvec::SmallVec::<[u8; 32]>::new(); //1 header, 4 ID
    my_addr_announce.write_all(CODE_CLIENT_ANNOUNCE)?; //header byte, this won't fail
    my_addr_announce.write_all(&id.to_le_bytes()[..])?; //this also won't fail
    if let Ok(_) = ws_send(&mut stream, &my_addr_announce, WS_BINARY) {
        for (theirid, other_stream) in zone.iter_mut() {
            if let Err(e) = ws_send(other_stream, &my_addr_announce, WS_BINARY){
                println!("Error {} sending announcement message", e);
            }
            if let Err(_) = full_list.write_all(&theirid.to_le_bytes()[..]){ break }
        }
        if let Ok(_) = ws_send(&mut stream, &full_list, WS_BINARY){
            println!("Client {} is zone {:X} ID {}", address, zoneid, id);
            zone.insert(id, stream);
            drop(stat); //release lock
            drop(full_list); //allow re-use of stack space
            while let Ok(rcvd) = ws_recv(&mut rcv_stream, &mut recvvec, &mut offsb) {
                println!("Received {} from {}", rcvd.len(), id);
                if let Ok(mut s) = state.lock() {
                    if let Some(conns) = s.get_mut(&zoneid) { if let Err(e) = do_one(conns, rcvd){
                        println!("Error handling ID {}: {}", id, e);
                        break;
                    }}
                }
            }
        }
    }
    println!("{} ({}) exited", id, address);
    my_addr_announce[0] = CODE_CLIENT_EXIT[0]; //change announcement message to an exit message
    if let Ok(mut stat) = state.lock(){ if let Some(conns) = stat.get_mut(&zoneid) {
        conns.remove(&id); //they closed so we close
        for tcp in conns.values_mut() {
            if let Err(e) = ws_send(tcp, &my_addr_announce, WS_BINARY){
                println!("Error sending exit message {}", e);
            }
        }
        if conns.len() == 0{
            stat.remove(&zoneid);
        }
    }}
    Ok(())
}
//Runs a simple STUN server
fn runstun(socket: std::net::UdpSocket) -> Result<()>{
    let mut buf = [0; 128];
    loop {
        let (len, src) = socket.recv_from(&mut buf)?;
        let stun = &mut buf[..len];
        if stun.len() < 20 || stun[0] != 0 || stun[1] != 1 {
            continue;
        }
        let mut bind_resp = [0; 0x2c];
        let mut end = 0x2c;
        (&mut bind_resp[0..4]).copy_from_slice(&[01, 01, 00, 0x18]); //response, initial attributes len
        (&mut bind_resp[4..0x14]).copy_from_slice(&stun[4..0x14]); //message cookie, transaction ID
        (&mut bind_resp[0x14..0x1a]).copy_from_slice(&[00, 0x20, 00, 0x14, 00, 02]); //len 20 type IPv6
        let p = src.port();
        let ports = [((p >> 8) as u8) ^ stun[4], ((p & 0xFF) as u8) ^ stun[5]]; //port masking
        (&mut bind_resp[0x1a..0x1c]).copy_from_slice(&ports); //port slice
        if let std::net::IpAddr::V6(v6add) = src.ip() {
            let ip = v6add.octets();
            let mut slc = [0; 0x10]; // = ip[:0x10] ^ stun[4:0x14]
            (&mut slc).iter_mut().enumerate().for_each(|(i,s)| *s = ip[i] ^ stun[4 + i]);
            (&mut bind_resp[0x1c..0x2c]).copy_from_slice(&slc[..]);
            if &ip[..0xc] == &[0,0,0,0,0,0,0,0,0,0,0xff,0xff]{ //ipv4 on ipv6 (linux is dumb)
                bind_resp[3] = 0x0c;
                bind_resp[0x17] = 0x08;
                bind_resp[0x19] = 0x01;
                end = 0x20;
                (&mut bind_resp[0x1c..0x20]).iter_mut().enumerate().for_each(|(i,s)| *s = ip[0xc + i] ^ stun[4 + i]);
            }
        }else if let std::net::IpAddr::V4(v4add) = src.ip() { //real IPv4
            bind_resp[3] = 0x0c;
            bind_resp[0x17] = 0x08;
            bind_resp[0x19] = 0x01;
            end = 0x20;
            let ip = v4add.octets();
            (&mut bind_resp[0x1c..0x20]).iter_mut().enumerate().for_each(|(i,s)| *s = ip[0xc + i] ^ stun[4 + i]);
        }
        socket.send_to(&bind_resp[..end], &src)?;
    }
}

fn main() -> Result<()>{
    if let Ok(s) = std::net::UdpSocket::bind(std::net::SocketAddrV6::new(std::net::Ipv6Addr::UNSPECIFIED, 5678, 0, 0)) {
        std::thread::spawn(move || runstun(s)); //Run a STUN server in another thread (IPv6)
    }
    if let Ok(s) = std::net::UdpSocket::bind(std::net::SocketAddrV4::new(std::net::Ipv4Addr::UNSPECIFIED, 5678)) {
        std::thread::spawn(move || runstun(s)); //Run a STUN server in another thread (IPv4 if necessary)
    }
    
    let state: State = Default::default();
    let astate = Arc::new(Mutex::new(state));
    let state2 = Arc::clone(&astate);
    std::thread::spawn(move || {
        loop {
            std::thread::sleep(std::time::Duration::from_secs(15));
            if let Ok(mut s) = state2.lock() {
                for (_k, zone) in s.iter_mut() {
                    for (_key, stream) in zone.iter_mut() {
                        let _ = ws_send(stream, b"PING", WS_PING); //send pings
                    }
                }
            }
        }
    });
    let listener = TcpListener::bind(std::net::SocketAddrV4::new(std::net::Ipv4Addr::UNSPECIFIED, 64479))?; //Run main TCP/HTTP/WebSocket server
    while let Ok((stream, address)) = listener.accept() {
        let thread_state = Arc::clone(&astate);
        std::thread::spawn(move || do_it(stream, thread_state, address));
    }
    Ok(())
}

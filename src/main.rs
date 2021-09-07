//  Prawned
//  Server for an HTML-based anonymity network
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
use rand_core::{RngCore, OsRng};
use p256::{PublicKey, ecdh::EphemeralSecret};
use p256::elliptic_curve::sec1::ToEncodedPoint;
//use p256::ecdsa::{SigningKey, VerifyingKey, Signature, signature::Signer, signature::Verifier};
use aes_gcm_siv::Aes256GcmSiv; // Or `Aes128GcmSiv`
use aes_gcm_siv::aead::{AeadInPlace, NewAead, generic_array::GenericArray};
use aes_gcm_siv::aead::heapless::{Vec, consts::U2048};

struct State {
    conns: std::collections::HashMap<[u8; 33], (TcpStream, SocketAddr, Aes256GcmSiv, [u8; 12])>,
    fwds: std::collections::HashMap<[u8; 33], ([u8; 33], [u8; 33])>,
    sends: std::collections::HashMap<[u8; 33], std::vec::Vec<std::vec::Vec<u8>>>,
    pubkey: [u8; 33],
}

//static CODE_NONE: &[u8; 1] = b"\x00";
static CODE_FULL_LIST: &[u8; 1] = b"\x01";
static CODE_CLIENT_EXIT: &[u8; 1] = b"\x02";
//static CODE_CLIENT_RTC_REQUEST: &[u8; 1] = b"\x03";
static CODE_CLIENT_FWD: &[u8; 1] = b"\x04";
//CODE_CLIENT_RTC_RESPONSE = 5
static CODE_CLIENT_BROADCAST: &[u8; 1] = b"\x06";
static CODE_SEAL: &[u8; 1] = b"\x07";
//CODE_E2E_MSG = 8
static CODE_CLIENT_BROADCASTED: &[u8; 1] = b"\x09";
static CODE_REVERSE_FWD: &[u8; 1] = b"\x0a";
static CODE_PADDED: &[u8; 1] = b"\x0b";
static CODE_CLIENT_ANNOUNCE: &[u8; 1] = b"\x0c";
static CODE_CLIENT_FWD_NOW: &[u8; 1] = b"\x0d"; //non-delayed fwd (for setup)

//reads bytes if not read yet
fn check_len(len: &mut usize, s: &mut TcpStream, buf: &mut [u8], min: usize) -> Result<()> {
    if min > buf.len() {
        return Err(Error::from(ErrorKind::InvalidInput)); //can't fit into buf - your fault fail
    } else if *len < min {
        s.read_exact(&mut buf[*len..min])?;
        *len = min;
    }
    Ok(())
}

//receives a websocket message. Must fit inside buf, with headers
fn ws_recv<'a>(stream: &mut TcpStream, buf: &'a mut [u8], readb: &mut usize, offsb: &mut usize) -> Result<&'a mut [u8]> {
    for i in 0..(*readb - *offsb) {
        buf[i] = buf[i + *offsb]; //memmove it down
    }
    *readb -= *offsb;
    *offsb = 0;
    if *readb == 0 {
        *readb = stream.read(&mut buf[*readb..])?;
    };
    check_len(readb, stream, buf, 2)?;
    let (leng, offs) = if buf[1] & 0x7F == 127 {
        check_len(readb, stream, buf, 10)?; //make sure we can fit all this
        let lenbytes = [buf[2], buf[3], buf[4], buf[5], buf[6], buf[7], buf[8], buf[9]];
        (u64::from_be_bytes(lenbytes) as usize, 10) // More than 64k?
    } else if buf[1] & 0x7F == 126 {
        check_len(readb, stream, buf, 4)?;
        (buf[2] as usize * 256 + buf[3] as usize, 4)
    } else {
        ((buf[1] & 0x7F) as usize, 2)
    };
    *offsb = offs;
    let mut mask = [0; 4];
    let masked = buf[1] & 0x80 != 0;
    if masked {
        check_len(readb, stream, buf, *offsb + 4)?; //make sure we can fit
        (&mut mask[..]).copy_from_slice(&buf[*offsb..*offsb + 4]);
        *offsb += 4;
    }
    check_len(readb, stream, buf, *offsb + leng)?; //read the rest of the data if needed
    if masked {
        for i in 0..leng {
            buf[*offsb + i] ^= mask[i % 4]; //demask
        }
    }
    let res = &mut buf[*offsb..*offsb + leng];
    *offsb += leng; // now we've handled this much
    Ok(res) //return the read buf
}

//Sends a websocket message.
fn ws_send(stream: &mut TcpStream, sendable: &[u8]) -> Result<()> {
    let mut buf = [0; 2048];
    buf[0] = 0x82; //binary. Text would be 0x81
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
    let mut body = b"what";//&include_bytes!("../prawned_packed.html")[..];
    //let found_bod = std::fs::read("prawned.html").ok();
    //if let Some(b) = found_bod.as_ref(){
    //    body = &b[..];
    //}
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
    let mut buf = [0; 2048]; //we don't do cookies or anything, should be PLENTY - no need to alloc
    let bytes = stream.read(&mut buf)?; //the full GET is usually ~256 bytes
    //if the http is >2k or not in one read/tcp segment, it isn't a browser; they're messing with us
    let data = &buf[..bytes]; // so find \r\n\r\n or return error
    data.windows(4).position(|w| w == b"\r\n\r\n").ok_or(Error::from(ErrorKind::NotFound))?;
    if data.starts_with(b"GET / ") {
        handle_root(stream)?;
        return Ok(false);
    }
    let needle = b"Sec-WebSocket-Key: "; //find the header or return error
    let idx = data.windows(needle.len()).position(|w| w == needle).ok_or(Error::from(ErrorKind::NotFound))?;
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

fn queue_send(state: &mut State, key: &[u8; 33], val: std::vec::Vec<u8>) {
    if let None = state.conns.get(key){
        eprintln!("Trying to queue send of {} bytes but isn't a conn!", val.len());
        return;
    }
    if let Some(queued) = state.sends.get_mut(key) {
        queued.push(val);
    } else {
        let mut v = std::vec::Vec::with_capacity(1);
        v.push(val);
        state.sends.insert(*key, v);
    }
}
fn pad_send(pad: &mut [u8; 2048 - 128], val: &[u8], other_stream: &mut TcpStream, nonce: &mut [u8; 12], cipher: &mut Aes256GcmSiv){
    let mut v = val;
    if val.len() < pad.len() - 3 {
        pad[0] = 0xb;
        pad[1] = (val.len() & 0xFF) as u8;
        pad[2] = ((val.len() >> 8) & 0xFF) as u8;
        (&mut pad[3..3+val.len()]).copy_from_slice(&val[..]);
        v = &pad[..];
    }
    let _ = enc_ws_send(other_stream, nonce, cipher, v); //not much error handling we can do here - if stream is dead other code will clean it up
}
fn process_sends(state: &mut State) {
    let mut randbyte = [0];
    for (key, (other_stream, addr, cipher, nonce)) in state.conns.iter_mut() {
        let _ = std::fs::File::open("/dev/urandom").and_then(|mut f| f.read(&mut randbyte[..]));
        if randbyte[0] & 0x3 != 0 { continue }; // 1 in 4 chance of sending anything
        let mut pad = [0; 2048 - 128]; //space for encryption overhead
        if let Some(queue) = state.sends.get_mut(key){
            if let Some(queued) = queue.pop(){
                println!("sending queued {} bytes to {} padded to 1920", queued.len(), addr);  //legit client
                pad_send(&mut pad, &queued, other_stream, nonce, cipher);
                continue;
            }
        }
        let _ = enc_ws_send(other_stream, nonce, cipher, &pad[..]); //send dummy
    }
}

//handle a client message
fn do_one(state: &mut State, buf: &mut [u8], k: &EphemeralSecret) -> Result<()> {
    if buf.len() > 3 && buf[0] == CODE_PADDED[0] {
        let len = u16::from_le_bytes([buf[1], buf[2]]) as usize;
        if len > buf.len() - 3{
            eprintln!("too big for padded {} > {} - 3", len, buf.len());
            return Err(Error::from(ErrorKind::InvalidInput));
        }
        return do_one(state, &mut buf[3..(3+len)], k); //handle wrapping
    } else if buf.len() > 34 && (buf[0] == CODE_CLIENT_FWD[0] || buf[0] == CODE_CLIENT_FWD_NOW[0]) {
        //println!("forward cmd {} bytes", buf.len());
        let mut key = [0; 33];
        (&mut key[..]).copy_from_slice(&buf[1..34]);
        if let Some((other_stream, addr, cipher, nonce)) = state.conns.get_mut(&key){
            if buf[0] == CODE_CLIENT_FWD[0] {
                println!("queuing {} bytes to {} code {}", buf.len() - 34, addr, buf[0]);  //legit client
                queue_send(state, &key, (&buf[34..]).to_vec()); //delay send
            } else {
                println!("direct forwarding {} bytes to {} code {}", buf.len() - 34, addr, buf[0]);  //legit client
                pad_send(&mut [0; 2048 - 128], &buf[34..], other_stream, nonce, cipher);
            }
        }else if let Some((next_hop, intermed_key)) = state.fwds.get(&key){
            if let Some((_, addr, _, _)) = state.conns.get(next_hop){
                let mut b64buf = [0; 44]; //base64 of 33 bytes=44 bytes
                base64::encode_config_slice(&key, base64::STANDARD, &mut b64buf);
                let mut b64intermed = [0; 44]; //base64 of 33 bytes=44 bytes
                base64::encode_config_slice(&intermed_key, base64::STANDARD, &mut b64intermed);
                println!("forwarding {} bytes to {} via hop {} ({})", buf.len() - 34, std::str::from_utf8(&b64buf).unwrap_or(""), addr, std::str::from_utf8(&b64intermed).unwrap_or(""));  //next client
                (&mut buf[1..34]).copy_from_slice(&intermed_key[..]); //change destination to intermed key
                if &intermed_key[..] == &state.pubkey[..] { //it's us
                    println!("self forward");
                    return do_one(state, buf, k);
                }
                let nh2 = *next_hop;
                queue_send(state, &nh2, buf.to_vec()); //delay send
            } else {
                println!("Lost reverse forward! {:?}", next_hop);
            }
        }else{
            let mut b64buf = [0; 44]; //base64 of 33 bytes=44 bytes
            base64::encode_config_slice(&key, base64::STANDARD, &mut b64buf);
            println!("Couldn't find {} maybe they left", std::str::from_utf8(&b64buf).unwrap_or(""));
        }
    } else if buf.len() > 34 + 16 && buf[0] == CODE_SEAL[0] { //unseal it
        let mut cli_pkey = [0; 33];
        (&mut cli_pkey[..33]).copy_from_slice(&buf[1..34]);
        let cli_pubkey = if let Ok(pk) = PublicKey::from_sec1_bytes(&cli_pkey[..]) { pk } else {
            eprintln!("too short for sealed");
            return Err(Error::from(ErrorKind::InvalidInput)); //can't fit into buf - your fault fail
        };
        let key = k.diffie_hellman(&cli_pubkey);
        let cipher = Aes256GcmSiv::new(GenericArray::from_slice(key.as_bytes()));
        let (_, rcvd) = buf.split_at_mut(34);
        let (msg, tag) = rcvd.split_at_mut(rcvd.len() - 16); //tag size = 16
        if let Ok(_) = cipher.decrypt_in_place_detached(GenericArray::from_slice(&[0; 12]), b"", msg, aes_gcm_siv::Tag::from_slice(tag)) {
            println!("De-sealed - processing {} bytes", msg.len());
            return do_one(state, msg, k);
        } else {
            eprintln!("Bad seal decrypt bytes [{}, {} ... {}] k [{}, {}, ...]", rcvd[0], rcvd[1], rcvd[rcvd.len() - 1], key.as_bytes()[0], key.as_bytes()[1]);
        }
    } else if buf.len() > 34 && buf[0] == CODE_CLIENT_BROADCAST[0] {
        println!("Broadcasting {} bytes", buf.len()); //TODO: delay
        buf[0] = CODE_CLIENT_BROADCASTED[0];
        for (_key, (other_stream, _addr, their_cipher, other_nonce)) in state.conns.iter_mut() {
            enc_ws_send(other_stream, other_nonce, their_cipher, buf)?;
        }
    } else if buf.len() >= 1 + 33 + 33 + 33 + 64 && buf[0] == CODE_REVERSE_FWD[0] {
        // [8, [ultimate dest pkey], [next hop forward pkey], [intermed_key], [signature]
        // TODO: validate that next hop is signed by ultimate destination
        // TODO: version check against any others
        let mut cli_pkey = [0; 33];
        (&mut cli_pkey[..]).copy_from_slice(&buf[1..34]);
        let mut dest_pkey = [0; 33];
        (&mut dest_pkey[..]).copy_from_slice(&buf[34..34+33]);
        let mut intermed_key = [0; 33];
        (&mut intermed_key[..]).copy_from_slice(&buf[34+33..34+33+33]);
                let mut b64buf = [0; 44]; //base64 of 33 bytes=44 bytes
                base64::encode_config_slice(&cli_pkey, base64::STANDARD, &mut b64buf);
                let mut b64intermed = [0; 44]; //base64 of 33 bytes=44 bytes
                base64::encode_config_slice(&dest_pkey, base64::STANDARD, &mut b64intermed);
        println!("Setting up reverse forward {} -> {}", std::str::from_utf8(&b64buf).unwrap_or(""), std::str::from_utf8(&b64intermed).unwrap_or(""));
        if state.conns.get(&dest_pkey).is_some() { //verify we have conn to next hop
            state.fwds.insert(cli_pkey, (dest_pkey, intermed_key)); //then add to forward table
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

fn increment_nonce(nonce: &mut [u8; 12]){
    let mut i = 11;
    while i > 0 && nonce[i] == 0xff {
        nonce[i] = 0;
        i -= 1;
    }
    nonce[i] = nonce[i].wrapping_add(1); //increment nonce
}

fn enc_ws_send(stream: &mut TcpStream, nonce: &mut [u8; 12], cipher: &Aes256GcmSiv, msg: &[u8]) -> Result<()> {
    increment_nonce(nonce);
    //println!("enc_ws_send {} bytes", msg.len());
    let noncea = GenericArray::from_slice(nonce); // 96-bits; unique per message
    let mut buffer: Vec<u8, U2048> = Vec::new();
    buffer.extend_from_slice(msg).map_err(|_| Error::from(ErrorKind::InvalidInput))?;
    cipher.encrypt_in_place(&noncea, b"", &mut buffer).map_err(|_| Error::from(ErrorKind::InvalidInput))?;
    ws_send(stream, &buffer)
}

//Handles a client connection
fn do_it(mut stream: TcpStream, state: Arc<Mutex<State>>, address: SocketAddr, k: &EphemeralSecret) -> Result<()> {
    if ! setup_websocket_server_connection(&mut stream)?{
        return Ok(()); //not a websocket
    }
    ws_send(&mut stream, k.public_key().to_encoded_point(true).as_bytes())?; //send our pubkey
    let mut nonce = [0; 12];
    OsRng.fill_bytes(&mut nonce);
    ws_send(&mut stream, &nonce)?;
    let mut buf = [0; 2048];
    let (mut readb, mut offsb) = (0, 0);
    let kmsg = ws_recv(&mut stream, &mut buf[..], &mut readb, &mut offsb)?; //Receive their sec1 key, then parse and calculate DH
    let mut cli_pkey = [0; 33];
    (&mut cli_pkey[..33.min(kmsg.len())]).copy_from_slice(&kmsg[..33.min(kmsg.len())]);
    let cli_pubkey = if let Ok(pk) = PublicKey::from_sec1_bytes(&cli_pkey[..]) { pk } else {
        return Err(Error::from(ErrorKind::InvalidInput)); //can't fit into buf - your fault fail
    };
    //now we both calculate shared key and init AES-256-GCM-SIV
    let shared_key = k.diffie_hellman(&cli_pubkey);
    //println!("shared key {:?}", shared_key.as_bytes());
    let cipher = Aes256GcmSiv::new(GenericArray::from_slice(shared_key.as_bytes()));
    let nmsg = ws_recv(&mut stream, &mut buf[..], &mut readb, &mut offsb)?; //Receive their nonce
    let mut cli_nonce = [0; 12];
    (&mut cli_nonce[..12.min(nmsg.len())]).copy_from_slice(&nmsg[..12.min(nmsg.len())]);
    println!("Client at {} connected", address);

    let mut rcv_stream = stream.try_clone()?; //another view of the same connection for sending threads
    let mut my_addr_announce = smallvec::SmallVec::<[u8; 64]>::new(); //1 header, 33 key
    my_addr_announce.write_all(CODE_CLIENT_ANNOUNCE)?; //header byte
    my_addr_announce.write_all(&cli_pkey[..])?;
    let mut full_list = smallvec::SmallVec::<[u8; 2048]>::new();
    full_list.write_all(CODE_FULL_LIST)?;
    let mut stat = if let Ok(s) = state.lock() { s } else {
        return Err(Error::from(ErrorKind::InvalidInput)); // shouldn't happen on most platforms
    };
    for (key, (other_stream, _addr, their_cipher, other_nonce)) in stat.conns.iter_mut() {
        enc_ws_send(other_stream, other_nonce, their_cipher, &my_addr_announce)?;
        full_list.write_all(&key[..])?;
    }
    enc_ws_send(&mut stream, &mut nonce, &cipher, &full_list)?;
                let mut b64buf = [0; 44]; //base64 of 33 bytes=44 bytes
                base64::encode_config_slice(&cli_pkey, base64::STANDARD, &mut b64buf);
                println!("Client {} is {}", address, std::str::from_utf8(&b64buf).unwrap_or(""));
    stat.conns.insert(cli_pkey.clone(), (stream, address.clone(), cipher.clone(), nonce));
    drop(stat); //release lock, AFTER THIS POINT RECEIVE ONLY ON THIS THREAD - NO DIRECT SENDS
    drop(full_list); //allow re-use of stack space
    while let Ok(rcvd) = ws_recv(&mut rcv_stream, &mut buf[..], &mut readb, &mut offsb) {
        increment_nonce(&mut cli_nonce);
        //try to decrypt with cli_nonce
        let noncea = GenericArray::from_slice(&cli_nonce); // 96-bits; unique per message
        if rcvd.len() < 16 { //tag size = 16
            println!("Received {} from {} - too short", rcvd.len(), address);
            let _ = rcv_stream.write_all(b"\x88\x00"); //exit sequence if the stream's alive, ignore if not
            break; //and bail
        }
        let (msg, tag) = rcvd.split_at_mut(rcvd.len() - 16); //tag size = 16
        if let Ok(_) = cipher.decrypt_in_place_detached(noncea, b"", msg, aes_gcm_siv::Tag::from_slice(tag)) {
            if let Ok(mut s) = state.lock() {
                if let Err(e) = do_one(&mut s, msg, k){
                    eprintln!("Error handling: {}", e);
                }
            }
        } else {
            eprintln!("Bad decrypt nonce {:?} bytes [{}, {} ... {}] key {:?}", noncea, rcvd[0], rcvd[1], rcvd[rcvd.len() - 1], shared_key.as_bytes());
            break;
        }
    }
    println!("{} exited", address);
    my_addr_announce[0] = CODE_CLIENT_EXIT[0]; //change announcement message to an exit message
    if let Ok(mut stat) = state.lock() {
        stat.conns.remove(&cli_pkey); //they closed so we close
        stat.sends.remove(&cli_pkey); //clean any pending sends up too
        for (ref mut tcp, _a, ref their_cipher, other_nonce) in stat.conns.values_mut() {
            enc_ws_send(tcp, other_nonce, their_cipher, &my_addr_announce)?;
        }
    }
    Ok(())
}

fn main() -> Result<()>{
    let mut pk = [0; 33];
    let secret = Arc::new(EphemeralSecret::random(&mut OsRng));
    (&mut pk[..]).copy_from_slice(secret.public_key().to_encoded_point(true).as_bytes());
    let mut b64buf = [0; 44]; //base64 of 33 bytes=44 bytes
    base64::encode_config_slice(&pk, base64::STANDARD, &mut b64buf);
    println!("Initialized my pubkey: {}", std::str::from_utf8(&b64buf).unwrap_or(""));
    let state = Arc::new(Mutex::new(State{
        conns: Default::default(),
        fwds:  Default::default(),
        sends: Default::default(),
        pubkey: pk
    }));
    let listener = TcpListener::bind("0.0.0.0:26135")?;
    let state2 = Arc::clone(&state);
    std::thread::spawn(move || {
        let start = std::time::Instant::now();
        let mut elapsed = std::time::Duration::new(0, 0);
        loop {
            std::thread::sleep(std::time::Duration::new(1, 0) - std::time::Duration::new(0, elapsed.subsec_nanos()));
            if let Ok(mut state_lock) = state2.lock(){
                process_sends(&mut state_lock);  //after waiting until the next round second
            }
            elapsed = start.elapsed();
        }
    });
    while let Ok((stream, address)) = listener.accept() {
        let (thread_state, secret2) = (Arc::clone(&state), Arc::clone(&secret));
        std::thread::spawn(move || do_it(stream, thread_state, address, &secret2));
    }
    Ok(())
}

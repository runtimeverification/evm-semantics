open Constants.K

let h = Cryptokit.Hash.keccak 256

let gethex = function
| '0' -> 0
| '1' -> 1
| '2' -> 2
| '3' -> 3
| '4' -> 4
| '5' -> 5
| '6' -> 6
| '7' -> 7
| '8' -> 8
| '9' -> 9
| 'a' -> 10
| 'b' -> 11
| 'c' -> 12
| 'd' -> 13
| 'e' -> 14
| 'f' -> 15

let hook_keccak256 c lbl sort config ff = match c with
  [String hex] ->
  let nbytes = (String.length hex) / 2 in
  let ibuf = Buffer.create nbytes in
  (for i = 0 to nbytes - 1 do 
    let high = String.get hex (i*2) in
    let low = String.get hex (i*2+1) in
    let byte = ((gethex high) * 16) + (gethex low) in
    Buffer.add_char ibuf (char_of_int byte)
   done);
  let buf = Buffer.create 64 in
  let bytes = Cryptokit.hash_string h (Buffer.contents ibuf) in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02x" (int_of_char c))) bytes;
  [String (Buffer.contents buf)]

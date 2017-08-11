open Constants.K


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
  let h = Cryptokit.Hash.keccak 256 in
(*  let nbytes = (String.length hex) / 2 in
  let ibuf = Buffer.create nbytes in
  (for i = 0 to nbytes - 1 do 
    let high = String.get hex (i*2) in
    let low = String.get hex (i*2+1) in
    let byte = ((gethex high) * 16) + (gethex low) in
    Buffer.add_char ibuf (char_of_int byte)
   done);
  let bytes = Cryptokit.hash_string h (Buffer.contents ibuf) in *)
  let bytes = Cryptokit.hash_string h hex in
  let buf = Buffer.create 64 in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02x" (int_of_char c))) bytes;
  [String (Buffer.contents buf)]

let hook_ecdsaRecover c lbl sort config ff = match c with
  [String hash], [Int v], [String r], [String s] ->
  if String.length r <> 32 || String.length s <> 32 then [String ""] else
  let signatureString = r ^ s in
  let signatureArray = Array.init 64 (fun idx -> signatureString.[idx]) in
  let signatureBuffer = Bigarray.Array1.of_array Bigarray.char Bigarray.c_layout signatureArray in
  let context = Secp256k1.Context.create [Secp256k1.Context.Sign; Secp256k1.Context.Verify] in
  let v = Z.to_int v in
  if v < 27 || v > 28 then [String ""] else
  let signature = Secp256k1.RecoverableSign.of_compact_exn context signatureBuffer (v - 27) in
  if String.length hash <> 32 then [String ""] else
  let messageArray = Array.init 32 (fun idx -> hash.[idx]) in
  let messageBuffer = Bigarray.Array1.of_array Bigarray.char Bigarray.c_layout messageArray in
  let publicKey = Secp256k1.RecoverableSign.recover context signature messageBuffer in
  let publicBuffer = Secp256k1.Public.to_bytes ~compress:false context publicKey in
  if Bigarray.Array1.dim publicBuffer <> 65 then failwith "invalid public key length" else
  let publicStr = String.init 64 (fun idx -> Bigarray.Array1.get publicBuffer (idx + 1)) in
  [String publicStr]


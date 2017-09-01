open Constants.K

let do_hash str h =
  let bytes = Cryptokit.hash_string h str in
  let buf = Buffer.create ((String.length bytes) * 2) in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%02x" (int_of_char c))) bytes;
  [String (Buffer.contents buf)]

let hook_sha256 c lbl sort config ff = match c with
  [String str] ->
  let h = Cryptokit.Hash.sha2 256 in
  do_hash str h
| _ -> failwith "sha256"

let hook_keccak256 c lbl sort config ff = match c with
  [String str] ->
  let h = Cryptokit.Hash.keccak 256 in
  do_hash str h
| _ -> failwith "keccak256"

let hook_ripemd160 c lbl sort config ff = match c with
  [String str] ->
  let h = Cryptokit.Hash.ripemd160 () in
  do_hash str h
| _ -> failwith "ripemd160"

let hook_ecdsaRecover c lbl sort config ff = match c with
  [String hash], [Int v], [String r], [String s] ->
  if String.length r <> 32 || String.length s <> 32 then [String ""] else
  let signatureString = r ^ s in
  let signatureArray = Array.init 64 (fun idx -> signatureString.[idx]) in
  let signatureBuffer = Bigarray.Array1.of_array Bigarray.char Bigarray.c_layout signatureArray in
  let context = Secp256k1.Context.create [Secp256k1.Context.Sign; Secp256k1.Context.Verify] in
  (try
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
  with Failure _ -> [String ""]
  |    Z.Overflow -> [String ""])
| _ -> failwith "ecdsaRecover"

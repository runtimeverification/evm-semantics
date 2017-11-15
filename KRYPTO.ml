open Constants
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
    let signature = Secp256k1.RecoverableSign.of_compact_exn context (v - 27) signatureBuffer in
    if String.length hash <> 32 then [String ""] else
    let messageArray = Array.init 32 (fun idx -> hash.[idx]) in
    let messageBuffer = Bigarray.Array1.of_array Bigarray.char Bigarray.c_layout messageArray in
    let publicKey = match Secp256k1.RecoverableSign.recover context signature messageBuffer with
        Some k -> k
      | None -> failwith "key recovery failed" in
    let publicBuffer = Secp256k1.Public.to_bytes ~compress:false context publicKey in
    if Bigarray.Array1.dim publicBuffer <> 65 then failwith "invalid public key length" else
    let publicStr = String.init 64 (fun idx -> Bigarray.Array1.get publicBuffer (idx + 1)) in
    [String publicStr]
  with Failure _ -> [String ""]
  |    Z.Overflow -> [String ""])
| _ -> failwith "ecdsaRecover"

exception InvalidPoint

let get_pt k = match k with
| [KApply2(Lbl'LPar'_'Comm'_'RPar'_KRYPTO, [Int x], [Int y])] ->
    if Z.equal x Z.zero && Z.equal y Z.zero then BN128Curve.Infinite else
    if (Z.lt x BN128Elements.field_modulus && Z.lt y BN128Elements.field_modulus) then
      let pt = BN128Curve.Finite (BN128Elements.FQ.create x, BN128Elements.FQ.create y) in
      if BN128Curve.G1.is_on_curve pt then pt else raise InvalidPoint
    else raise InvalidPoint
| _ -> invalid_arg "not a point"

let get_pt_g2 k = match k with
| [KApply4(Lbl'LPar'_x_'Comm'_x_'RPar'_KRYPTO, [Int x1], [Int x2], [Int y1], [Int y2])] ->
    if Z.equal x1 Z.zero && Z.equal x2 Z.zero && Z.equal y1 Z.zero && Z.equal y2 Z.zero then BN128Curve.Infinite else
    if (Z.lt x1 BN128Elements.field_modulus && Z.lt x2 BN128Elements.field_modulus && Z.lt y1 BN128Elements.field_modulus && Z.lt y2 BN128Elements.field_modulus) then
      let pt = BN128Curve.Finite (BN128Elements.FQP.create_fq2 [|x1; x2|], BN128Elements.FQP.create_fq2 [|y1; y2|]) in
      if BN128Curve.G2.is_on_curve pt then pt else raise InvalidPoint
    else raise InvalidPoint
| _ -> invalid_arg "not a point"

let project_pt pt = let x, y = match pt with
| BN128Curve.Finite (xf, yf) -> BN128Elements.FQ.to_z xf, BN128Elements.FQ.to_z yf
| BN128Curve.Infinite -> Z.zero, Z.zero
in [KApply2(Lbl'LPar'_'Comm'_'RPar'_KRYPTO, [Int x], [Int y])]

let hook_bn128valid c lbl sort config ff =
  try
    let _ = get_pt c in
    [Bool true]
  with InvalidPoint -> [Bool false]

let hook_bn128g2valid c lbl sort config ff =
  try
    let _ = get_pt_g2 c in
    [Bool true]
  with InvalidPoint -> [Bool false]

let hook_bn128add c lbl sort config ff = match c with
  k1, k2 ->
  let pt1 = get_pt k1 in
  let pt2 = get_pt k2 in
  project_pt (BN128Curve.G1.add pt1 pt2)

let hook_bn128mul c lbl sort config ff = match c with
  k,
  [Int s] ->
  let pt1 = get_pt k in
  project_pt (BN128Curve.G1.mul pt1 s)
| _ -> failwith "bn128mul"

let hook_bn128ate c lbl sort config ff = match c with
  [List(_, _, a)], [List(_, _, b)] ->
  let g1a = List.map get_pt a in
  let g2b = List.map get_pt_g2 b in
  let fq12c = List.map BN128Pairing.pairing (List.combine g2b g1a) in
  let product = List.fold_left BN128Elements.FQP.mulp BN128Elements.FQP.one_fq12 fq12c in
  [Bool (product = BN128Elements.FQP.one_fq12)]
| _ -> failwith "bn128ate"

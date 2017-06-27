open Constants.K

let h = Cryptokit.Hash.keccak 256

let hook_keccak256 c lbl sort config ff = 
  let buf = Buffer.create 64 in
  let bytes = match c with
    [String input] -> Cryptokit.hash_string h input in
  String.iter (fun c -> Buffer.add_string buf (Printf.sprintf "%x" (int_of_char c))) bytes;
  [String (Buffer.contents buf)]

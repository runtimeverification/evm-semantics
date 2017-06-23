open Constants.K

let h = Cryptokit.Hash.keccak 256

let hook_keccak256 c lbl sort config ff = match c with
  [String input] -> [String (Cryptokit.hash_string h input)]

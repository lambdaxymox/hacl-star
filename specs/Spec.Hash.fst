module Spec.Hash

open Spec.SHA2

#reset-options "--max_fuel 0 --z3rlimit 25"

inline_for_extraction
private let parameters a = match a with
  | SHA2_224 -> Spec.SHA2.parameters224
  | SHA2_256 -> Spec.SHA2.parameters256
  | SHA2_384 -> Spec.SHA2.parameters384
  | SHA2_512 -> Spec.SHA2.parameters512

let hash_w a = match a with
  | SHA2_224 -> Spec.SHA2.hash_w (parameters a)
  | SHA2_256 -> Spec.SHA2.hash_w (parameters a)
  | SHA2_384 -> Spec.SHA2.hash_w (parameters a)
  | SHA2_512 -> Spec.SHA2.hash_w (parameters a)

let size_block a = match a with
  | SHA2_224 -> Spec.SHA2.size_block (parameters a)
  | SHA2_256 -> Spec.SHA2.size_block (parameters a)
  | SHA2_384 -> Spec.SHA2.size_block (parameters a)
  | SHA2_512 -> Spec.SHA2.size_block (parameters a)

let size_hash a = match a with
  | SHA2_224 -> (parameters a).size_hash
  | SHA2_256 -> (parameters a).size_hash
  | SHA2_384 -> (parameters a).size_hash
  | SHA2_512 -> (parameters a).size_hash

let max_input a = match a with
  | SHA2_224 -> Spec.SHA2.max_input (parameters a)
  | SHA2_256 -> Spec.SHA2.max_input (parameters a)
  | SHA2_384 -> Spec.SHA2.max_input (parameters a)
  | SHA2_512 -> Spec.SHA2.max_input (parameters a)

let init a = match a with
  | SHA2_224 -> Spec.SHA2.init (parameters a)
  | SHA2_256 -> Spec.SHA2.init (parameters a)
  | SHA2_384 -> Spec.SHA2.init (parameters a)
  | SHA2_512 -> Spec.SHA2.init (parameters a)

let update_block a b h = match a with
  | SHA2_224 -> Spec.SHA2.update_block (parameters a) b h
  | SHA2_256 -> Spec.SHA2.update_block (parameters a) b h
  | SHA2_384 -> Spec.SHA2.update_block (parameters a) b h
  | SHA2_512 -> Spec.SHA2.update_block (parameters a) b h

let update_multi a n b h = match a with
  | SHA2_224 -> Spec.SHA2.update_multi (parameters a) n b h
  | SHA2_256 -> Spec.SHA2.update_multi (parameters a) n b h
  | SHA2_384 -> Spec.SHA2.update_multi (parameters a) n b h
  | SHA2_512 -> Spec.SHA2.update_multi (parameters a) n b h

let update_last a n l b h = match a with
  | SHA2_224 -> Spec.SHA2.update_last (parameters a) n l b h
  | SHA2_256 -> Spec.SHA2.update_last (parameters a) n l b h
  | SHA2_384 -> Spec.SHA2.update_last (parameters a) n l b h
  | SHA2_512 -> Spec.SHA2.update_last (parameters a) n l b h

let finish a h = match a with
  | SHA2_224 -> Spec.SHA2.finish (parameters a) h
  | SHA2_256 -> Spec.SHA2.finish (parameters a) h
  | SHA2_384 -> Spec.SHA2.finish (parameters a) h
  | SHA2_512 -> Spec.SHA2.finish (parameters a) h

let hash a s = match a with
  | SHA2_224 -> Spec.SHA2.hash' (parameters a) s
  | SHA2_256 -> Spec.SHA2.hash' (parameters a) s
  | SHA2_384 -> Spec.SHA2.hash' (parameters a) s
  | SHA2_512 -> Spec.SHA2.hash' (parameters a) s

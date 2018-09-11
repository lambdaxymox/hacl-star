module Lib.Vec128

module ST = FStar.HyperStack.ST
open FStar.HyperStack
open FStar.HyperStack.All
open Lib.IntTypes
open LowStar.Buffer
type lbuffer a len = b:buffer a{length b == len}
type bytes = buffer FStar.UInt8.t
type lbytes l = b:bytes {length b == l} 

val vec128 : Type0

noextract
val ni_aes_enc: vec128 -> vec128 -> vec128
noextract
val ni_aes_enc_last: vec128 -> vec128 -> vec128
noextract
val ni_aes_keygen_assist: vec128 -> uint8 -> vec128

noextract
val ni_clmul: vec128 -> vec128 -> uint8 -> vec128

noextract
val vec128_xor: vec128 -> vec128 -> vec128
noextract
val vec128_or: vec128 -> vec128 -> vec128
noextract
val vec128_shift_left: vec128 -> size_t -> vec128
noextract
val vec128_shift_right: vec128 -> size_t -> vec128
noextract
val vec128_shift_left64: vec128 -> size_t -> vec128
noextract
val vec128_shift_right64: vec128 -> size_t -> vec128
noextract
val vec128_shuffle32: vec128 -> uint8 -> vec128
noextract
val vec128_shuffle32_spec: uint8 -> uint8 -> uint8 -> uint8 -> uint8

noextract
val vec128_load_le: b:lbytes 16 -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))

noextract
val vec128_load_be: b:lbytes 16 -> ST vec128
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  h1 == h0))
			   
noextract
val vec128_store_le: b:lbytes 16 -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc_buffer b) h0 h1))

noextract
val vec128_store_be: b:lbytes 16 -> vec128 -> ST unit
			   (requires (fun h -> live h b))
			   (ensures (fun h0 _ h1 ->  live h1 b /\ modifies (loc_buffer b) h0 h1))

noextract
val vec128_insert32: vec128 -> uint32 -> uint8 -> vec128
noextract
val vec128_zero: vec128


noextract val bit_mask64: uint64 -> uint64
module Hacl.Blake2b

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer

module Spec = Spec.Blake2
module Impl = Hacl.Impl.Blake2b


let hash_wp = lbuffer uint64 8
let block_p = lbuffer uint8 64


val blake2b_init:
    #vkk:size_t
  -> hash:hash_wp
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 64} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h k
                   /\ LowStar.Buffer.disjoint hash k
                   /\ LowStar.Buffer.disjoint k hash))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_init Spec.Blake2B (v kk) h0.[k] (v nn)))

let blake2b_init #vkk hash k kk nn = Impl.blake2b_init #vkk hash k kk nn


val blake2b_update_block:
    hash:hash_wp
  -> prev:size_t{size_v prev <= Spec.max_limb Spec.Blake2B}
  -> d:block_p ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h d
                   /\ LowStar.Buffer.disjoint hash d))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.blake2_update_block Spec.Blake2B (v prev) h0.[d] h0.[hash]))

let blake2b_update_block hash prev d = Impl.blake2b_update_block hash prev d


val blake2b_update_last:
    #vlen: size_t
  -> hash: hash_wp
  -> prev: size_t{v prev <= Spec.max_limb Spec.Blake2B}
  -> last: lbuffer uint8 (v vlen)
  -> len: size_t{v len <= Spec.size_block Spec.Blake2B /\ len == vlen} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h last
                   /\ LowStar.Buffer.disjoint hash last))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer hash) h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_update_last Spec.Blake2B (v prev) (v len) h0.[last] h0.[hash]))

let blake2b_update_last #vlen hash prev last len = Impl.blake2b_update_last #vlen hash prev last len


val blake2b_finish:
    #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> hash: hash_wp
  -> nn: size_t{1 <= v nn /\ v nn <= 64 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h hash
                   /\ LowStar.Buffer.live h output
                   /\ LowStar.Buffer.disjoint output hash
                   /\ LowStar.Buffer.disjoint hash output))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2_finish Spec.Blake2B h0.[hash] (v nn)))

let blake2b_finish #vnn output hash nn = Impl.blake2b_finish #vnn output hash nn


val blake2b:
    output: buffer uint8
  -> d: buffer uint8
  -> ll: size_t{length d == v ll}
  -> k: buffer uint8
  -> kk: size_t{length k == v kk /\ v kk <= 32 /\ (if v kk = 0 then v ll < pow2 128 else v ll + 64 < pow2 128)}
  -> nn:size_t{v nn == length output /\ 1 <= v nn /\ v nn <= 64} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h output
                   /\ LowStar.Buffer.live h d
                   /\ LowStar.Buffer.live h k
                   /\ LowStar.Buffer.disjoint output d
                   /\ LowStar.Buffer.disjoint output k))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2b h0.[d] (v kk) h0.[k] (v nn)))

let blake2b output d ll k kk nn = Impl.blake2b output d ll k kk nn

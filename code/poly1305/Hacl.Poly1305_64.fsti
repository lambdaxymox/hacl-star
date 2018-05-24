module Hacl.Poly1305_64

open FStar.HyperStack.All
open FStar.Mul
open FStar.Endianness
open FStar.Buffer
open FStar.UInt64

open FStar.Ghost
open FStar.Seq
open FStar.HyperStack
open FStar.Endianness
open FStar.Buffer
open Hacl.Cast

open Hacl.Spec.Endianness

module HS = FStar.HyperStack
module I = Hacl.Impl.Poly1305_64
module S = Hacl.Spec.Poly1305_64
module Poly = Hacl.Standalone.Poly1305_64


#reset-options "--max_fuel 0 --z3rlimit 100"

(* Type Aliases *)
let uint8_p = Buffer.buffer Hacl.UInt8.t
let uint64_t = FStar.UInt64.t
private let op_String_Access h (b:uint8_p{live h b}) = reveal_sbytes (as_seq h b)

(* Type Aliases *)
type key = k:uint8_p{length k = 32}

type state = I.poly1305_state
type live_state (h:mem) (st:state) = I.live_st h st
type stable (h:mem) (st:state) = live_state h st /\ S.red_45 (as_seq h I.(st.h)) /\ S.red_44 (as_seq h I.(st.r))

private let get_key (st:state) = I.(st.r)
private let get_accumulator (st:state) = I.(st.h)

#reset-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 10"

val mk_state:
  r:buffer Hacl.UInt64.t{length r = 3} -> acc:buffer Hacl.UInt64.t{length acc = 3 /\ disjoint r acc} ->
  Stack state
    (requires (fun h -> live h r /\ live h acc))
    (ensures (fun h0 st h1 -> h0 == h1 /\ I.(st.r) == r /\ I.(st.h) == acc /\ I.live_st h1 st))

val init:
  st:state ->
  k:uint8_p{length k >= 16} ->
  Stack unit
    (requires (fun h -> live h k /\ live_state h st))
    (ensures (fun h0 _ h1 -> modifies_2 (get_key st) (get_accumulator st) h0 h1 /\ stable h1 st))

val update_block:
  st:state ->
  m:uint8_p{length m = 16} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))

module A = Hacl.Spec.Bignum.AddAndMultiply

private type before_finish h st = A.(live_state h st /\ bounds (as_seq h (get_accumulator st)) p44 p44 p42)

val update:
  st:state ->
  m:uint8_p ->
  num_blocks:FStar.UInt32.t{length m >= 16 * UInt32.v num_blocks} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 updated_log h1 -> modifies_1 (get_accumulator st) h0 h1 /\ stable h1 st))

val update_last:
  st:state ->
  m:uint8_p ->
  len:UInt32.t{UInt32.v len < 16 /\ UInt32.v len <= length m} ->
  Stack unit
    (requires (fun h -> stable h st /\ live h m))
    (ensures  (fun h0 _ h1 -> modifies_1 (get_accumulator st) h0 h1 /\ before_finish h1 st))

val finish:
  st:state ->
  mac:uint8_p{length mac = 16} ->
  k:uint8_p{length k = 16} ->
  Stack unit
    (requires (fun h -> before_finish h st /\ live h mac /\ live h k))
    (ensures (fun h0 _ h1 -> modifies_1 mac h0 h1))

val crypto_onetimeauth:
  mac:uint8_p{length mac = 16} ->
  input:uint8_p{disjoint input mac} ->
  len:uint64_t{v len < pow2 32 /\ v len = length input} ->
  key:uint8_p{disjoint mac key /\ length key = 32} ->
  Stack unit
    (requires (fun h -> live h mac /\ live h input /\ live h key))
    (ensures  (fun h0 _ h1 -> live h1 mac /\ modifies_1 mac h0 h1 /\ live h0 input /\ live h0 key
      /\ h1.[mac] == Spec.Poly1305.poly1305 h0.[input] h0.[key]))

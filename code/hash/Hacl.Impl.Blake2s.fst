module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Spec.Lib.IntTypes
open Spec.Lib.IntSeq
open Spec.Lib.IntBuf
open Spec.Lib.IntBuf.Lemmas
open Spec.Lib.IntBuf.LoadStore

module ST = FStar.HyperStack.ST
module LSeq = Spec.Lib.IntSeq
module Spec = Spec.Blake2s


///
/// STATUS
/// ------
///
/// 0. The code is proven until `blake2s_internal`.
/// 1. Rewrite update_sub to be in the correct order.
/// 2. Lemmata need to be proven and moved back to the libraries.
///


///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
let op_String_Access #a #len m b = as_lseq #a #len b m

///
/// Helper lemmata
///

val lemma_cast_to_u64: x:uint32 -> Lemma
  (requires (True))
  (ensures  (to_u64 #U32 x == u64 (uint_v #U32 x)))
  [SMTPat (to_u64 #U32 x)]

let lemma_cast_to_u64 x = admit()

val lemma_modifies0_is_modifies1: #a0:Type -> #len0:size_nat -> b0:lbuffer a0 len0 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (h0 == h1 ==> modifies1 b0 h0 h1))
let lemma_modifies0_is_modifies1 #a0 #len0 b0 h0 h1 = admit()


val lemma_modifies0_is_modifies2: #a0:Type -> #a1:Type -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (h0 == h1 ==> modifies2 b0 b1 h0 h1))
let lemma_modifies0_is_modifies2 #a0 #a1 #len0 #len1 b0 b1 h0 h1 = admit()


val lemma_modifies1_is_modifies2: #a0:Type -> #a1:Type -> #len0:size_nat -> #len1:size_nat -> b0:lbuffer a0 len0 -> b1:lbuffer a1 len1 -> h0:mem -> h1:mem -> Lemma
  (requires (True))
  (ensures  (modifies1 b0 h0 h1 ==> modifies2 b0 b1 h0 h1))
let lemma_modifies1_is_modifies2 #a0 #a1 #len0 #len1 b0 b1 h0 h1 = admit()


val lemma_repeati: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> i:size_nat{i < n} -> Lemma
  (requires True)
  (ensures  (f i (repeati #a i f init) == repeati #a (i + 1) f init))

let lemma_repeati #a n f init i = admit()


val lemma_repeati_zero: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> Lemma
  (requires True)
  (ensures  (init == repeati #a 0 f init))

let lemma_repeati_zero #a n f init = admit()


val lemma_uint_to_nat_equals_u32_of_v_of_size_t: #t:inttype -> x:uint_t t -> Lemma
  (requires True)
  (ensures (Spec.Lib.RawIntTypes.uint_to_nat #t x == (uint_v x)))
  [SMTPat (Spec.Lib.RawIntTypes.uint_to_nat #t x)]
let lemma_uint_to_nat_equals_u32_of_v_of_size_t #t x = admit()


val lemma_value_mixed_size_addition: x:size_t -> y:size_nat -> Lemma
  (requires True)
  (ensures (v (x +. (size y)) == v x + y))
  [SMTPat (v (x +. (size y)) == v x + y)]
let lemma_value_mixed_size_addition x y = admit()

(* val lemma_modifies2_of_subs_is_modifies1: #h0:mem -> #h1:mem -> #a:Type0 -> #len:size_nat -> #pos0:size_nat -> #len0:size_nat{pos0 + len0 < len} -> #pos1:size_nat -> #len1:size_nat{pos1 + len1 <= len} -> buf:lbuffer a len -> sub0:lbuffer a len0 -> sub1:lbuffer a len1 -> *)
(*   Lemma *)
(*     (requires (True)) *)
(*     (ensures  ((modifies2 sub0 sub1 h0 h1 *)
(*                /\ sub0 == sub buf (size pos0) (size len0) *)
(*                /\ sub1 == sub buf (size pos1) (size len1)) ==> modifies1 buf h0 h1)) *)

(* let lemma_modifies2_of_subs_is_modifies1 #h0 #h1 #a #len #pos0 #len0 #pos1 #len1 buf sub0 sub1 = admit() *)

val lemma_modifies2_trans: #h0:mem -> #h1:mem -> #h2:mem -> #a0:Type0 -> #a1:Type0 -> #len0:size_nat -> #len1:size_nat -> buf0:lbuffer a0 len0 -> buf1:lbuffer a1 len1 ->
  Lemma
    (requires (modifies2 buf0 buf1 h0 h1 /\ modifies2 buf0 buf1 h1 h2))
    (ensures  (modifies2 buf0 buf1 h0 h2))

let lemma_modifies2_trans #h0 #h1 #h2 #a0 #a1 #len0 #len1 buf0 buf1 = admit()


(* Functions to add to the libraries *)
val update_sub: #a:Type0 -> #len:size_nat -> #xlen:size_nat -> i:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == xlen} -> x:lbuffer a xlen ->
  Stack unit
    (requires (fun h -> live h i /\ live h x))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 i h0 h1
                         /\ h1.[i] == Spec.Lib.IntSeq.update_sub #a #len h0.[i] (v start) (v n) h0.[x]))

[@ Substitute]
let update_sub #a #len #olen i start n x =
  let i' = sub i start n in
  copy i' n x


///
/// Blake2s
///

(* Define algorithm parameters *)
type working_vector = lbuffer uint32 Spec.size_block_w
type message_block_w = lbuffer uint32 Spec.size_block_w
type message_block = lbuffer uint8 Spec.size_block
type hash_state = lbuffer uint32 Spec.size_hash_w
type idx = n:size_t{size_v n < 16}
type iv_t = lbuffer uint32 Spec.size_hash_w
type sigma_elt = n:uint32{uint_v n < 16}
type sigma_t = lbuffer sigma_elt 160

let vsize_state = Spec.size_hash_w + Spec.size_const_iv + Spec.size_const_sigma
let pos_hash = size 0
let pos_const_iv = size Spec.size_hash_w
let pos_const_sigma = (size Spec.size_hash_w) +. (size Spec.size_const_iv)
type state = lbuffer uint32 vsize_state


assume val get_hash: state -> Tot hash_state
assume val get_const_iv: state -> Tot iv_t
assume val get_const_sigma: state -> Tot sigma_t



(* Definition of constants *)
inline_for_extraction val create_const_iv: unit -> StackInline iv_t
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> creates1 r h0 h1 /\
		                  preserves_live h0 h1 /\
		                  modifies1 r h0 h1 /\
		                  as_lseq r h1 == Spec.const_iv))

inline_for_extraction let create_const_iv () =
  assert_norm(List.Tot.length Spec.list_iv = 8);
  createL Spec.list_iv


inline_for_extraction val create_const_sigma: unit -> StackInline sigma_t
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> creates1 r h0 h1 /\
		                  preserves_live h0 h1 /\
		                  modifies1 r h0 h1 /\
		                  as_lseq r h1 == Spec.const_sigma))

inline_for_extraction let create_const_sigma () =
  assert_norm(List.Tot.length Spec.list_sigma = 160);
  createL Spec.list_sigma


(* Define algorithm functions *)
val g1: wv:working_vector -> a:idx -> b:idx -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 h0.[wv] (v a) (v b) r))
let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:working_vector -> a:idx -> b:idx -> x:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 h0.[wv] (v a) (v b) x))
let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (add_mod #U32 wv_a wv_b) x


val blake2_mixing : wv:working_vector -> a:idx -> b:idx -> c:idx -> d:idx -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_mixing h0.[wv] (v a) (v b) (v c) (v d) x y))

let blake2_mixing wv a b c d x y =
  g2 wv a b x;
  g1 wv d a Spec.r1;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r2;
  g2 wv a b y;
  g1 wv d a Spec.r3;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r4


#reset-options "--max_fuel 0 --z3rlimit 150"

val blake2_round1 : wv:working_vector -> m:message_block_w -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                  /\ disjoint wv m /\ disjoint wv const_sigma
                  /\ disjoint m wv /\ disjoint const_sigma wv
                  /\ h.[const_sigma] == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_round1 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 wv m i const_sigma =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = sub #sigma_elt #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 4) (size  8) (size 12) (m.(s.(size 0))) (m.(s.(size 1)));
  blake2_mixing wv (size 1) (size 5) (size  9) (size 13) (m.(s.(size 2))) (m.(s.(size 3)));
  blake2_mixing wv (size 2) (size 6) (size 10) (size 14) (m.(s.(size 4))) (m.(s.(size 5)));
  blake2_mixing wv (size 3) (size 7) (size 11) (size 15) (m.(s.(size 6))) (m.(s.(size 7)))


val blake2_round2 : wv:working_vector -> m:message_block_w -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                  /\ disjoint wv m /\ disjoint wv const_sigma
                  /\ disjoint m wv /\ disjoint const_sigma wv
                  /\ h.[const_sigma] == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 wv m i const_sigma =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s = sub #sigma_elt #160 #16 const_sigma start_idx (size 16) in
  blake2_mixing wv (size 0) (size 5) (size 10) (size 15) (m.(s.(size 8))) (m.(s.(size 9)));
  blake2_mixing wv (size 1) (size 6) (size 11) (size 12) (m.(s.(size 10))) (m.(s.(size 11)));
  blake2_mixing wv (size 2) (size 7) (size  8) (size 13) (m.(s.(size 12))) (m.(s.(size 13)));
  blake2_mixing wv (size 3) (size 4) (size  9) (size 14) (m.(s.(size 14))) (m.(s.(size 15)))


val blake2_round : wv:working_vector -> m:message_block_w -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ disjoint wv m /\ disjoint wv const_sigma
                   /\ disjoint m wv /\ disjoint const_sigma wv
                   /\ h.[const_sigma] == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round h0.[m] (v i) h0.[wv]))

// [@ (CConst "const_sigma")]
let blake2_round wv m i const_sigma =
  blake2_round1 wv m i const_sigma;
  blake2_round2 wv m i const_sigma


val blake2_compress1 : wv:working_vector ->
  s:hash_state -> m:message_block_w ->
  offset:uint64 -> flag:Spec.last_block_flag -> const_iv:iv_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv /\ live h const_iv
                     /\ h.[const_iv] == Spec.const_iv
                     /\ disjoint wv s /\ disjoint wv m /\ disjoint wv const_iv
                     /\ disjoint s wv /\ disjoint m wv /\ disjoint const_iv wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.Blake2s.blake2_compress1 h0.[wv] h0.[s] h0.[m] offset flag))

let blake2_compress1 wv s m offset flag const_iv =
  update_sub wv (size 0) (size 8) s;
  update_sub wv (size 8) (size 8) const_iv;
  let low_offset = to_u32 #U64 offset in
  let high_offset = to_u32 #U64 (offset >>. u32 32) in
  // BB. Note that using the ^. operator here would break extraction !
  let wv_12 = logxor #U32 wv.(size 12) low_offset in
  let wv_13 = logxor #U32 wv.(size 13) high_offset in
  let wv_14 = logxor #U32 wv.(size 14) (u32 0xFFFFFFFF) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


val blake2_compress2 :
  wv:working_vector -> m:message_block_w -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ live h const_sigma
                   /\ h.[const_sigma] == Spec.const_sigma
                   /\ disjoint wv m /\ disjoint wv const_sigma
                   /\ disjoint m wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 h0.[wv] h0.[m]))


//[@ Substitute ]
let blake2_compress2 wv m const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size Spec.rounds_in_f) wv
    (fun hi ->  Spec.blake2_round hi.[m])
    (fun i ->
      blake2_round wv m i const_sigma;
      lemma_repeati Spec.rounds_in_f (Spec.blake2_round h0.[m]) h0.[wv] (v i))


val blake2_compress3_inner :
  wv:working_vector -> i:size_t{size_v i < 8} -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3_inner h0.[wv] (v i) h0.[s]))

//[@ Substitute ]
let blake2_compress3_inner wv i s const_sigma =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  // BB. Note that using the ^. operator here would break extraction !
  let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


val blake2_compress3 :
  wv:working_vector -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv /\ live h const_sigma
                     /\ h.[const_sigma] == Spec.const_sigma
                     /\ disjoint wv s /\ disjoint wv const_sigma
                     /\ disjoint s wv /\ disjoint const_sigma wv))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3 h0.[wv] h0.[s]))

let blake2_compress3 wv s const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 (size 8) s
    (fun hi -> Spec.blake2_compress3_inner hi.[wv])
    (fun i -> blake2_compress3_inner wv i s const_sigma;
           lemma_repeati 8 (Spec.blake2_compress3_inner h0.[wv]) h0.[s] (v i))


val blake2_compress :
  s:hash_state -> m:message_block_w ->
  offset:uint64 -> f:Spec.last_block_flag -> const_iv:iv_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h const_iv /\ live h const_sigma
                         /\ h.[const_sigma] == Spec.const_sigma
                         /\ h.[const_iv] == Spec.const_iv
                         /\ disjoint s m /\ disjoint s const_sigma /\ disjoint s const_iv
                         /\ disjoint m s /\ disjoint const_sigma s /\ disjoint const_iv s))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1
                         /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress h0.[s] h0.[m] offset f))

let blake2_compress s m offset flag const_iv const_sigma =
  (**) let hinit = ST.get () in
  alloc1 #hinit (size 16) (u32 0) s
  (fun h0 ->
    let s0 = h0.[s] in
    let m0 = h0.[m] in
    (fun _ sv -> sv == Spec.Blake2s.blake2_compress s0 m0 offset flag))
  (fun wv ->
    blake2_compress1 wv s m offset flag const_iv;
    blake2_compress2 wv m const_sigma;
    blake2_compress3 wv s const_sigma)


val blake2s_update_block:
    st:state
  -> dd_prev:size_t
  -> d:message_block ->
  Stack unit
    (requires (fun h -> live h st /\ live h d
                   /\ (let const_iv = sub st pos_const_iv (size Spec.size_const_iv) in
                      let const_sigma = sub st pos_const_sigma (size Spec.size_const_sigma) in
                        h.[const_iv] == Spec.const_iv
                      /\ h.[const_sigma] == Spec.const_sigma)))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1
                         /\ (let s = sub st pos_hash Spec.size_hash_w in
                         h1.[s] == Spec.blake2s_update_block (v dd_prev) h0.[d] h0.[s])))

let blake2s_update_block s dd_prev d const_iv const_sigma =
  let h0 = ST.get () in
  alloc1 #h0 (size 16) (u32 0) s
  (fun h ->
    let d0 = h.[d] in
    let s0 = h.[s] in
    (fun _ sv -> sv == Spec.blake2s_update_block (v dd_prev) d0 s0))
  (fun block ->
    uints_from_bytes_le block d;
    let offset = to_u64 (size_to_uint32 (dd_prev +. (size 1))) *. (to_u64 (size Spec.size_block)) in
    blake2_compress s block offset false const_iv const_sigma
  )


val blake2s_init_hash:
    #vkk:size_nat
  -> s:lbuffer uint32 8
  -> kk:size_t{v kk <= 32 /\ v kk = vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
     (requires (fun h -> live h s))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                          /\ h1.[s] == Spec.Blake2s.blake2s_init_hash h0.[s] (v kk) (v nn)))

let blake2s_init_hash #vkk s kk nn =
  let s0 = s.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (u32 8) in
  let s0' = s0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  s.(size 0) <- s0'


val blake2s_init:
    #vkk:size_nat
  -> k:lbuffer uint8 vkk
  -> kk:size_t{v kk <= 32 /\ v kk = vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  StackInline state
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> True))

let blake2s_init #vkk k kk nn =
  let st = create (size size_state) (u32 0) in
  let s = sub #uint32 #size_state #Spec.size_hash_w st (size 0) (size Spec.size_hash_w) in
  let st_const_iv = sub st (size Spec.size_hash_w) (size Spec.size_hash_w) in
  let st_const_sigma = sub st (size (Spec.size_hash_w + Spec.size_hash_w)) (size 160) in
  let h0 = ST.get () in
  alloc1_with #h0 (size 8) Spec.const_iv create_const_iv st
  (fun h -> (fun _ _ -> True))
  (fun const_iv ->
    let h0 = ST.get () in
    alloc1_with #h0 (size 160) Spec.const_sigma create_const_sigma st
    (fun h -> (fun _ _ -> True))
    (fun const_sigma ->
      copy st (size Spec.size_hash_w) st_const_iv;
      copy st (size Spec.size_hash_w) st_const_sigma;
      let h0 = ST.get () in
      alloc1 #h0 (size Spec.size_block) (u8 0) st
      (fun h -> (fun _ sv -> True))
      (fun key_block ->
        blake2s_init_hash #vkk st kk nn;
        if kk =. (size 0) then ()
        else begin
          update_sub key_block (size 0) kk k;
          blake2s_update_block st (size 0) key_block const_iv const_sigma end
      )
    )
  );
  st


val blake2s_update_multi_iteration:
    s:hash_state
  -> dd_prev:size_t
  -> dd:size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d:lbuffer uint8 (v dd * Spec.size_block)
  -> i:size_t{v i + 1 <= v dd}
  -> const_iv:iv_t
  -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> live h s /\ live h d /\ live h const_iv /\ live h const_sigma
                     /\ h.[const_sigma] == Spec.const_sigma
                     /\ h.[const_iv] == Spec.const_iv
                     /\ disjoint s d /\ disjoint d s
                     /\ disjoint s const_sigma /\ disjoint s const_iv
                     /\ disjoint const_sigma s /\ disjoint const_iv s))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2s_update_multi_iteration (v dd_prev) (v dd) h0.[d] (v i) h0.[s]))

let blake2s_update_multi_iteration st dd_prev dd d i const_iv const_sigma =
  let block = sub d (i *. size Spec.size_block) (size Spec.size_block) in
  blake2s_update_block st (dd_prev +. i) block const_iv const_sigma


val blake2s_update_multi:
    s: hash_state
  -> dd_prev: size_t
  -> dd: size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d: lbuffer uint8 (size_v dd * Spec.size_block)
  -> const_iv:iv_t
  -> const_sigma:sigma_t ->
   Stack unit
     (requires (fun h -> live h s /\ live h d /\ live h const_iv /\ live h const_sigma
                    /\ h.[const_sigma] == Spec.const_sigma
                    /\ h.[const_iv] == Spec.const_iv
                    // Disjointness for s
                    /\ disjoint s d /\ disjoint d s
                    /\ disjoint s const_iv /\ disjoint const_iv s
                    /\ disjoint s const_sigma /\ disjoint const_sigma s))
     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1
                          /\ h1.[s] == Spec.blake2s_update_multi (v dd_prev) (v dd) h0.[d] h0.[s]))

let blake2s_update_multi s dd_prev dd d const_iv const_sigma =
  (**) let h0 = ST.get () in
  loop #h0 dd s
  (fun hi ->
    let d0 = h0.[d] in
    let s0 = h0.[s] in
    (fun i s -> Spec.Blake2s.blake2s_update_multi (v dd_prev) (v dd) d0 s0))
  (fun i ->
    blake2s_update_multi_iteration s dd_prev dd d i const_iv const_sigma;
    lemma_repeati (v dd) (Spec.blake2s_update_multi_iteration (v dd_prev) (v dd) h0.[d]) h0.[s] (v i))



val blake2s_update_last:
    #vlen: size_nat
  -> s: lbuffer uint32 8
  -> ll: size_t
  -> len: size_t
  -> last: lbuffer uint8 vlen
  -> flag_key: bool
  -> const_iv: iv_t
  -> const_sigma: sigma_t ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 s h0 h1))

let blake2s_update_last #vlen s ll len last fk const_iv const_sigma =
  (**) let h0 = ST.get () in
  alloc1 #h0 (size Spec.size_block) (u8 0) s
  (fun h ->
    (fun _ r -> True)// r == Spec.blake2s_internal3 s0 (v dd) d0 (v ll) (v kk) (v nn))
  )
  (fun last_block ->
    (**) let h0 = ST.get () in
    alloc1 #h0 (size Spec.size_block_w) (u32 0) s
    (fun h ->
      (fun _ r -> True)// r == Spec.blake2s_internal3 s0 (v dd) d0 (v ll) (v kk) (v nn))
    )
    (fun last_block_w ->
      update_sub last_block (size 0) len last;
      uint32s_from_bytes_le #16 last_block_w last_block;
      let ll64 = to_u64 #U32 (size_to_uint32 ll) in
      let ll_plus_block_bytes64 = ll64 +. (to_u64 #U32 (size_to_uint32 (size Spec.size_block))) in
      (**) lemma_value_mixed_size_addition ll Spec.size_block;
      if not fk then
        blake2_compress s last_block_w ll64 true const_iv const_sigma
      else
        blake2_compress s last_block_w ll_plus_block_bytes64 true const_iv const_sigma
    )
  )


val blake2s_finish:
    #vnn: size_nat
  -> output: lbuffer uint8 vnn
  -> st: lbuffer uint32 8
  -> nn: size_t{v nn = vnn} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 st h0 h1))

let blake2s_finish #vnn output s nn =
  (**) let h0 = ST.get () in
  alloc1 #h0 (size 32) (u8 0) output
  (fun h ->
    (fun _ r -> True)// r == Spec.blake2s_internal3 s0 (v dd) d0 (v ll) (v kk) (v nn))
  )
  (fun full ->
    uints_to_bytes_le full s;
    update_sub output (size 0) nn full)



val blake2s:
    #vll: size_nat
  -> #vkk: size_nat
  -> #vnn: size_nat
  -> output: lbuffer uint8 vnn
  -> d: lbuffer uint8 vll
  -> ll: size_t{v ll + 2 * Spec.size_block <= max_size_t /\ v ll = vll}
  -> kk: size_t{v kk <= 32 /\ v kk = vkk}
  -> k: lbuffer uint8 vkk
  -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ v nn = v nn} ->
  Stack unit
    (requires (fun h -> True))
    (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1))

let blake2s #vll #vkk #vnn output d ll kk k nn =
  let fk = if kk =. (size 0) then false else true in
  let rem = ll %. (size Spec.size_block) in
  let nblocks = ll /. (size Spec.size_block) in
  let blocks = sub #uint8 #vll #(v nblocks * Spec.size_block) d (size 0) (nblocks *. (size Spec.size_block)) in
  let last = sub d (nblocks *. (size Spec.size_block)) rem in
  if  ll =. (size 0) && kk =. (size 0) then begin
    let h0 = ST.get () in
    alloc1 #h0 (size Spec.size_block) (u8 0) output
    (fun h -> (fun _ r -> True))
    (fun data ->
      let h0 = ST.get () in
      let s = blake2s_init #vkk k kk nn in
      blake2s_update_last #(v rem) s ll (size Spec.size_block) data fk
      blake2s_finish #vnn output s nn) end
  else
    let s = blake2s_init #vkk k kk nn in
    let nprev = if kk =. (size 0) then (size 0) else (size 1) in
    blake2s_update_multi s nprev nblocks d;
    blake2s_update_last #(v rem) s ll rem last fk;
    blake2s_finish #vnn output s nn

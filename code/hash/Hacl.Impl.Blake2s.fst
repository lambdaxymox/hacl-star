module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.PQ.Buffer

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Spec = Spec.Blake2s
(* module Lemmas = Hacl.Impl.Lemmas *)

module B = LowStar.Buffer

val lemma_repeati: #a:Type -> n:size_nat -> f:(i:size_nat{i < n}  -> a -> Tot a) -> init:a -> i:size_nat{i < n} -> Lemma
  (requires True)
  (ensures  (f i (Seq.repeati #a i f init) == Seq.repeati #a (i + 1) f init))

let lemma_repeati #a n f init i = admit()


///
/// Helper functions
///

(* Operators *)
inline_for_extraction let v = size_v
inline_for_extraction let index (x:size_nat) = size x
unfold let op_String_Access #a #r1 #r2 m b = B.as_seq #a #r1 #r2 b m

(* (\* Functions to add to the libraries *\) *)
(* inline_for_extraction *)
(* val update_sub: #a:Type0 -> #len:size_nat -> #xlen:size_nat -> i:lbuffer a len -> start:size_t -> n:size_t{v start + v n <= len /\ v n == xlen} -> x:lbuffer a xlen -> *)
(*   Stack unit *)
(*     (requires (fun h -> B.live h i /\ B.live h x)) *)
(*     (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer i) h0 h1 *)
(*                          /\ h1.[i] == Seq.update_sub #a #len h0.[i] (v start) (v n) h0.[x])) *)

(* inline_for_extraction *)
(* let update_sub #a #len #olen i start n x = *)
(*   let buf = sub i start n in *)
(*   copy buf n x *)

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
type sigma_elt = n:size_t{size_v n < 16}
type sigma_t = lbuffer sigma_elt 160

noeq type state = {
  hash: hash_state;
  const_iv: iv_t;
  const_sigma: sigma_t;
}


noextract val state_invariant: h:mem -> st:state -> Type0
let state_invariant h st =
    B.live h st.hash /\ B.live h st.const_iv /\ B.live h st.const_sigma
  /\ B.disjoint st.hash st.const_iv
  /\ B.disjoint st.hash st.const_sigma
  /\ B.disjoint st.const_iv st.const_sigma
  /\ B.as_seq h st.const_iv == Spec.const_iv
  /\ B.as_seq h st.const_sigma == Spec.const_sigma

(* (\* Definition of constants *\) *)
inline_for_extraction val create_const_iv: unit -> StackInline iv_t
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> (*creates1 r h0 h1 /\ *)
		                  B.live h1 r /\
		                  B.modifies (B.loc_buffer r) h0 h1 /\
		                  B.as_seq h1 r == Spec.const_iv))

inline_for_extraction let create_const_iv () =
  assert_norm(List.Tot.length Spec.list_iv = 8);
  createL Spec.list_iv


inline_for_extraction val create_const_sigma: unit -> StackInline sigma_t
  (requires (fun h -> True))
  (ensures (fun h0 r h1 -> (* creates1 r h0 h1 /\ *)
		                  B.live h1 r /\
		                  B.modifies (B.loc_buffer r) h0 h1 /\
		                  B.as_seq h1 r == Spec.const_sigma))

inline_for_extraction let create_const_sigma () =
  assert_norm(List.Tot.length Spec.list_sigma = 160);
  createL Spec.list_sigma


(* Define algorithm functions *)
val g1: wv:working_vector -> a:idx -> b:idx -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> B.live h wv))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ B.as_seq h1 wv == Spec.g1 (B.as_seq h0 wv) (v a) (v b) r))
let g1 wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: wv:working_vector -> a:idx -> b:idx -> x:uint32 ->
  Stack unit
    (requires (fun h -> B.live h wv))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ B.as_seq h1 wv == Spec.g2 (B.as_seq h0 wv) (v a) (v b) x))
let g2 wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (add_mod #U32 wv_a wv_b) x


val blake2_mixing : wv:working_vector -> a:idx -> b:idx -> c:idx -> d:idx -> x:uint32 -> y:uint32 ->
  Stack unit
    (requires (fun h -> B.live h wv))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ B.as_seq h1 wv == Spec.blake2_mixing (B.as_seq h0 wv) (v a) (v b) (v c) (v d) x y))

let blake2_mixing wv a b c d x y =
  g2 wv a b x;
  g1 wv d a Spec.r1;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r2;
  g2 wv a b y;
  g1 wv d a Spec.r3;
  g2 wv c d (u32 0);
  g1 wv b c Spec.r4


#reset-options "--max_fuel 0 --z3rlimit 250"

val blake2_round1 : wv:working_vector -> m:message_block_w -> i:size_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> B.live h wv /\ B.live h m /\ B.live h const_sigma
                  /\ B.disjoint wv m /\ B.disjoint wv const_sigma
                  /\ (B.as_seq h const_sigma) == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ (B.as_seq h1 wv) == Spec.Blake2s.blake2_round1 (B.as_seq h0 wv) (B.as_seq h0 m) (v i)))

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
    (requires (fun h -> B.live h wv /\ B.live h m /\ B.live h const_sigma
                  /\ B.disjoint wv m /\ B.disjoint wv const_sigma
                  /\ B.as_seq h const_sigma == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ B.as_seq h1 wv == Spec.blake2_round2 (B.as_seq h0 wv) (B.as_seq h0 m) (v i)))

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
    (requires (fun h -> B.live h wv /\ B.live h m /\ B.live h const_sigma
                   /\ B.disjoint wv m /\ B.disjoint wv const_sigma
                   /\ B.as_seq h const_sigma == Spec.const_sigma))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ (B.as_seq h1 wv) == Spec.blake2_round (B.as_seq h0 m) (v i) (B.as_seq h0 wv)))
let blake2_round wv m i const_sigma =
  blake2_round1 wv m i const_sigma;
  blake2_round2 wv m i const_sigma


val blake2_compress1 : wv:working_vector ->
  s:hash_state -> m:message_block_w ->
  offset:uint64 -> flag:Spec.last_block_flag -> const_iv:iv_t ->
  Stack unit
    (requires (fun h -> B.live h s /\ B.live h m /\ B.live h wv /\ B.live h const_iv
                     /\ B.as_seq h const_iv == Spec.const_iv
                     /\ B.disjoint wv s /\ B.disjoint wv m /\ B.disjoint wv const_iv))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ B.as_seq h1 wv == Spec.Blake2s.blake2_compress1 (B.as_seq h0 wv) (B.as_seq h0 s) (B.as_seq h0 m) offset flag))

[@ Substitute ]
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
    (requires (fun h -> B.live h wv /\ B.live h m /\ B.live h const_sigma
                   /\ B.as_seq h const_sigma == Spec.const_sigma
                   /\ B.disjoint wv m /\ B.disjoint wv const_sigma))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer wv) h0 h1
                         /\ B.as_seq h1 wv == Spec.blake2_compress2 (B.as_seq h0 wv) (B.as_seq h0 m)))

[@ Substitute ]
let blake2_compress2 wv m const_sigma =
  (**) let h0 = ST.get () in
  Lib.PQ.Buffer.loop #h0 (size Spec.rounds_in_f) wv
    (fun hi ->  Spec.blake2_round (B.as_seq hi m))
    (fun i ->
      blake2_round wv m i const_sigma; admit())
      (* lemma_repeati Spec.rounds_in_f (Spec.blake2_round (B.as_seq h0 m) (B.as_seq h0 wv) (v i))) *)


val blake2_compress3_inner :
  wv:working_vector -> i:size_t{size_v i < 8} -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> B.live h s /\ B.live h wv /\ B.live h const_sigma))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer s) h0 h1
                         /\ B.as_seq h1 s == Spec.blake2_compress3_inner (B.as_seq h0 wv) (v i) (B.as_seq h0 s)))

[@ Substitute ]
let blake2_compress3_inner wv i s const_sigma =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  // BB. Note that using the ^. operator here would break extraction !
  let hi = logxor #U32 hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


val blake2_compress3 :
  wv:working_vector -> s:hash_state -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> B.live h s /\ B.live h wv /\ B.live h const_sigma
                     /\ B.as_seq h const_sigma == Spec.const_sigma
                     /\ B.disjoint wv s /\ B.disjoint wv const_sigma))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer s) h0 h1
                         /\ B.as_seq h1 s == Spec.blake2_compress3 (B.as_seq h0 wv) (B.as_seq h0 s)))

[@ Substitute ]
let blake2_compress3 wv s const_sigma =
  (**) let h0 = ST.get () in
  Lib.PQ.Buffer.loop #h0 (size 8) s
    (fun hi -> Spec.blake2_compress3_inner (B.as_seq hi wv))
    (fun i -> blake2_compress3_inner wv i s const_sigma; admit())
           (* lemma_repeati 8 (Spec.blake2_compress3_inner (B.as_seq h0 wv)) (B.as_seq h0 s) (v i)) *)

val blake2_compress :
  s:hash_state -> m:message_block_w ->
  offset:uint64 -> f:Spec.last_block_flag -> const_iv:iv_t -> const_sigma:sigma_t ->
  Stack unit
    (requires (fun h -> B.live h s /\ B.live h m /\ B.live h const_iv /\ B.live h const_sigma
                         /\ B.as_seq h const_sigma == Spec.const_sigma
                         /\ B.as_seq h const_iv == Spec.const_iv
                         /\ B.disjoint s m /\ B.disjoint s const_sigma /\ B.disjoint s const_iv))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer s) h0 h1
                         /\ B.as_seq h1 s == Spec.blake2_compress (B.as_seq h0 s) (B.as_seq h0 m) offset f))

let blake2_compress s m offset flag const_iv const_sigma =
  (**) let hinit = ST.get () in
  alloc #hinit (size 16) (u32 0) s
  (fun h0 ->
    let s0 = B.as_seq h0 s in
    let m0 = B.as_seq h0 m in
    (fun _ sv -> sv == Spec.Blake2s.blake2_compress s0 m0 offset flag))
  (fun wv ->
    let h0 = ST.get () in
    assume(B.as_seq h0 const_sigma == Spec.const_sigma
                         /\ B.as_seq h0 const_iv == Spec.const_iv);
    assert(B.live h0 wv);
    assume(B.disjoint wv s);
    assume(B.disjoint wv m);
    assume(B.disjoint wv const_iv);
    assume(B.disjoint wv const_sigma);
    blake2_compress1 wv s m offset flag const_iv;
    blake2_compress2 wv m const_sigma;
    blake2_compress3 wv s const_sigma
  )

val blake2s_update_block:
    st:state
  -> dd_prev:size_t{(size_v dd_prev + 1) * Spec.size_block <= max_size_t}
  -> d:message_block ->
  Stack unit
    (requires (fun h -> state_invariant h st /\ B.live h d
                   /\ B.disjoint st.hash d /\ B.disjoint d st.hash))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer st.hash) h0 h1
                         /\ B.as_seq h1 st.hash == Spec.blake2s_update_block (v dd_prev) (B.as_seq h0 d) (B.as_seq h0 st.hash)))

let blake2s_update_block st dd_prev d =
  let h0 = ST.get () in
  alloc #h0 (size 16) (u32 0) st.hash
  (fun h ->
    let d0 = B.as_seq h d in
    let s0 = B.as_seq h st.hash in
    (fun _ sv -> sv == Spec.blake2s_update_block (v dd_prev) d0 s0))
  (fun block ->
    Lib.Endianness.uints_from_bytes_le block (size Spec.size_block_w) d;
    let offset64 = to_u64 (size_to_uint32 ((dd_prev +. (size 1)) *. (size Spec.size_block))) in
    let hx = ST.get () in
    assume(B.disjoint st.hash block);
    assume(B.disjoint st.hash st.const_iv);
    assume(B.disjoint st.hash st.const_sigma);
    assume(B.as_seq hx st.const_sigma == Spec.const_sigma
         /\ B.as_seq hx st.const_iv == Spec.const_iv);

    blake2_compress st.hash block offset64 false st.const_iv st.const_sigma;
    admit()
  )


val blake2s_mkstate: unit ->
  StackInline state
    (requires (fun h -> True))
    (ensures  (fun h0 st h1 -> state_invariant h1 st
                          /\ B.modifies (B.loc_union (B.loc_buffer st.hash)
                                                    (B.loc_union (B.loc_buffer st.const_iv)
                                                                 (B.loc_buffer st.const_sigma))
                                       )h0 h1))

let blake2s_mkstate () =
  admit();
  {
    hash = create (size Spec.size_hash_w) (u32 0);
    const_iv = create_const_iv ();
    const_sigma = create_const_sigma ();
  }


val blake2s_init_hash:
    st:state
  -> kk:size_t{v kk <= 32}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
     (requires (fun h -> state_invariant h st))
     (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer st.hash) h0 h1
                          /\ B.as_seq h1 st.hash == Spec.Blake2s.blake2s_init_hash (B.as_seq h0 st.hash) (v kk) (v nn)))

let blake2s_init_hash st kk nn =
  let s0 = st.hash.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (u32 8) in
  let s0' = s0 ^. (u32 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  st.hash.(size 0) <- s0'


val blake2s_init:
  #vkk:size_t
  -> st:state
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ B.live h k
                   /\ B.disjoint st.hash k /\ B.disjoint k st.hash))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer st.hash) h0 h1
                         /\ B.as_seq h1 st.hash == Spec.Blake2s.blake2s_init (v kk) (B.as_seq h0 k) (v nn)))

[@ Substitute ]
let blake2s_init #vkk st k kk nn =
  let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) st.hash
  (fun h -> (fun _ sv ->
    let k0 = B.as_seq h0 k in
    sv == Spec.Blake2s.blake2s_init (v kk) k0 (v nn)))
  (fun key_block ->
    copy st.hash (size Spec.size_hash_w) st.const_iv;
    let hi = ST.get () in
    assume(state_invariant hi st);
    blake2s_init_hash st kk nn;
    if kk =. (size 0) then ()
    else begin
      assume(B.disjoint key_block k);
      update_sub key_block (size 0) kk k;
      let hi' = ST.get () in
      assume(state_invariant hi' st);
      assume(B.disjoint key_block st.hash);
      blake2s_update_block st (size 0) key_block end;
      admit()
  )


val blake2s_update_multi_iteration:
    st:state
  -> dd_prev:size_t
  -> dd:size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d:lbuffer uint8 (v dd * Spec.size_block)
  -> i:size_t{v i + 1 <= v dd} ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ B.live h d /\ B.disjoint st.hash d /\ B.disjoint d st.hash))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer st.hash) h0 h1
                         /\ B.as_seq h1 st.hash == Spec.blake2s_update_multi_iteration (v dd_prev) (v dd) (B.as_seq h0 d) (v i) (B.as_seq h0 st.hash)))

[@ Substitute ]
let blake2s_update_multi_iteration st dd_prev dd d i =
  let block = sub d (i *. size Spec.size_block) (size Spec.size_block) in
  blake2s_update_block st (dd_prev +. i) block


val blake2s_update_multi:
    st: state
  -> dd_prev: size_t
  -> dd: size_t{(v dd + v dd_prev) * Spec.size_block <= max_size_t}
  -> d: lbuffer uint8 (size_v dd * Spec.size_block) ->
   Stack unit
     (requires (fun h -> state_invariant h st
                    /\ B.live h d /\ B.disjoint st.hash d /\ B.disjoint d st.hash))
     (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer st.hash) h0 h1
                          /\ B.as_seq h1 st.hash == Spec.blake2s_update_multi (v dd_prev) (v dd) (B.as_seq h0 d) (B.as_seq h0 st.hash)))

let blake2s_update_multi st dd_prev dd d =
  (**) let h0 = ST.get () in
  loop #h0 dd st.hash
  (fun h -> let hd = B.as_seq h d in
    Spec.Blake2s.blake2s_update_multi_iteration (v dd_prev) (v dd) hd)
  (fun i ->
    blake2s_update_multi_iteration st dd_prev dd d i; admit())
    (* lemma_repeati (v dd) (Spec.blake2s_update_multi_iteration (v dd_prev) (v dd) h0.[d]) h0.[st.hash] (v i)) *)


val blake2s_update_last:
    #vlen: size_t
  -> st: state
  -> ll: size_t
  -> last: lbuffer uint8 (v vlen)
  -> len: size_t{v len <= Spec.size_block /\ len == vlen}
  -> flag_key: bool ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ B.live h last /\ B.disjoint st.hash last /\ B.disjoint last st.hash))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer st.hash) h0 h1
                         /\ B.as_seq h1 st.hash == Spec.Blake2s.blake2s_update_last (v ll) (v len) (B.as_seq h0 last) flag_key (B.as_seq h0 st.hash)))


let blake2s_update_last #vlen st ll last len fk =
  let ll64 : uint64 = to_u64 #U32 (size_to_uint32 ll) in
  let ll_plus_block_bytes64 = ll64 +. (u64 Spec.size_block) in
  assume(ll_plus_block_bytes64 == u64 (size_v ll + Spec.size_block));
  (**) let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) st.hash
  (fun h ->
    let hash0 = B.as_seq h0 st.hash in
    let last0 = B.as_seq h0 last in
    (fun _ r -> r == Spec.Blake2s.blake2s_update_last (v ll) (v len) last0 fk hash0)
  )
  (fun last_block ->
    let hi0 = ST.get() in
    assume(B.disjoint last_block last);
    update_sub last_block (size 0) len last;
    (**) let h1 = ST.get () in
    admit();
    alloc #h1 (size Spec.size_block_w) (u32 0) st.hash
    (fun h ->
      let hash1 = B.as_seq h1 st.hash in
      let last_block1 = B.as_seq h1 last_block in
      (fun _ r -> r == Spec.Blake2s.blake2s_update_last_block (v ll) last_block1 fk hash1)
    )
    (fun last_block_w ->
      Lib.Endianness.uint32s_from_bytes_le last_block_w (size 16) last_block;
      let hx = ST.get() in
      assume(B.disjoint last_block_w st.hash);
      assume(B.disjoint last_block_w st.const_iv);
      assume(B.disjoint last_block_w st.const_sigma);
      assume(B.as_seq hx st.const_sigma == Spec.const_sigma
           /\ B.as_seq hx st.const_iv == Spec.const_iv);
      if not fk then (
        blake2_compress st.hash last_block_w ll64 true st.const_iv st.const_sigma)
      else (
        blake2_compress st.hash last_block_w ll_plus_block_bytes64 true st.const_iv st.const_sigma)
    )
  )


val blake2s_update_last_empty:
  st: state ->
  Stack unit
    (requires (fun h -> state_invariant h st))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer st.hash) h0 h1
                         /\ (let data = Seq.create Spec.size_block (u8 0) in
                           B.as_seq h1 st.hash == Spec.Blake2s.blake2s_update_last (Spec.size_block) (Spec.size_block) data false (B.as_seq h0 st.hash))))

let blake2s_update_last_empty st =
  let h0 = ST.get () in
  alloc #h0 (size Spec.size_block) (u8 0) st.hash
  (fun h ->
    let hash0 = B.as_seq h st.hash in
    (fun _ r ->
      let data = Seq.create Spec.size_block (u8 0) in
      r ==  Spec.Blake2s.blake2s_update_last (Spec.size_block) (Spec.size_block) data false hash0))
  (fun data ->
      let hx = ST.get () in
      assume(state_invariant hx st);
      assume(B.disjoint data st.hash);
      blake2s_update_last #(size Spec.size_block) st (size Spec.size_block) data (size Spec.size_block) false;
      admit()
  )


val blake2s_finish:
    #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> st: state
  -> nn: size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> state_invariant h st
                   /\ B.live h output /\ B.disjoint output st.hash /\ B.disjoint st.hash output))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer output) h0 h1
                         /\ B.as_seq h1 output == Spec.Blake2s.blake2s_finish (B.as_seq h0 st.hash) (v nn)))

let blake2s_finish #vnn output s nn =
  (**) let h0 = ST.get () in
  alloc #h0 (size 32) (u8 0) output
  (fun h ->
    (fun _ r -> r == Spec.Blake2s.blake2s_finish (B.as_seq h0 s.hash) (v nn))
  )
  (fun full ->
    assume(B.disjoint full output);
    Lib.Endianness.uints_to_bytes_le full (size 8) s.hash;
    let final = sub full (size 0) nn in
    copy output nn final;
    admit())


val blake2s:
    #vll: size_t
  -> #vkk: size_t
  -> #vnn: size_t
  -> output: lbuffer uint8 (v vnn)
  -> d: lbuffer uint8 (v vll)
  -> ll: size_t{v ll + 2 * Spec.size_block <= max_size_t /\ ll == vll} // This could be relaxed
  -> k: lbuffer uint8 (v vkk)
  -> kk: size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> B.live h output /\ B.live h d /\ B.live h k
                   /\ B.disjoint output d /\ B.disjoint k output))
    (ensures  (fun h0 _ h1 -> B.modifies (B.loc_buffer output) h0 h1
                         /\ B.as_seq h1 output == Spec.Blake2s.blake2s (v ll) (B.as_seq h0 d) (v kk) (B.as_seq h0 k) (v nn)))

let blake2s #vll #vkk #vnn output d ll k kk nn =
  push_frame ();
  let st = blake2s_mkstate () in
  let h0 = ST.get () in
  assume(B.disjoint st.hash k);
  assume(B.disjoint st.hash output);
  let fk = if kk =. (size 0) then false else true in
  let rem = ll %. (size Spec.size_block) in
  let nblocks = ll /. (size Spec.size_block) in
  let blocks = sub #_ #_ #(v nblocks * Spec.size_block) d (size 0) (nblocks *. (size Spec.size_block)) in
  let last = sub #_ #_ #(v rem) d (nblocks *. (size Spec.size_block)) rem in
  blake2s_init #vkk st k kk nn;
  if ll =. (size 0) && kk =. (size 0) then blake2s_update_last_empty st
  else begin
    let nprev = if kk =. (size 0) then (size 0) else (size 1) in
    blake2s_update_multi st nprev nblocks d;
    blake2s_update_last #rem st ll last rem fk
  end;
  blake2s_finish #vnn output st nn;
  pop_frame();
  admit()


///
/// Experimental variant
///

(* inline_for_extraction val mkstate: *)
(*   #h0: mem -> *)
(*   #b: Type0 -> *)
(*   #w: Type0 -> *)
(*   #wlen: size_nat -> *)
(*   write: lbuffer w wlen -> *)
(*   spec:(h:mem -> GTot(r:b -> LSeq.lseq w (wlen) -> Type)) -> *)
(*   impl:(st:state -> *)
(*         Stack b *)
(*         (requires (fun h -> state_invariant h st *)
(* 		                 /\ preserves_live h0 h *)
(* 		                 /\ modifies3 st.hash st.const_iv st.const_sigma h0 h)) *)
(*         (ensures (fun h r h' -> preserves_live h h' *)
(*                            /\ modifies2 st.hash write h h' /\ *)
(* 			 spec h0 r (as_seq write h')))) -> *)
(*   Stack b *)
(*     (requires (fun h -> h == h0 /\ live h write)) *)
(*     (ensures (fun h0 r h1 -> preserves_live h0 h1 /\ *)
(* 		          modifies1 write h0 h1 /\ *)
(* 		          spec h0 r (as_seq write h1))) *)

(* let mkstate #h0 #b #w #wlen write spec impl = *)
(*   admit(); *)
(*   let h0 = ST.get () in *)
(*   alloc #h0 (size Spec.size_hash_w) (u32 0) write *)
(*   (fun h -> (fun _ sv -> True)) *)
(*   (fun hash -> *)
(*     let h0 = ST.get () in *)
(*     alloc_with #h0 (size 8) Spec.const_iv create_const_iv write *)
(*     (fun h -> (fun _ _ -> True)) *)
(*     (fun const_iv -> *)
(*       let h0 = ST.get () in *)
(*       alloc_with #h0 (size 160) Spec.const_sigma create_const_sigma write *)
(*       (fun h -> (fun _ _ -> True)) *)
(*       (fun const_sigma -> *)
(*         let st = {hash = hash; const_iv = const_iv; const_sigma = const_sigma} in *)
(*         impl st *)
(*       ) *)
(*     ) *)
(*   ) *)


(* val blake2s: *)
(*     #vll: size_t *)
(*   -> #vkk: size_t *)
(*   -> #vnn: size_t *)
(*   -> output: lbuffer uint8 (v vnn) *)
(*   -> d: lbuffer uint8 (v vll) *)
(*   -> ll: size_t{v ll + 2 * Spec.size_block <= max_size_t /\ ll == vll} // This could be relaxed *)
(*   -> k: lbuffer uint8 (v vkk) *)
(*   -> kk: size_t{v kk <= 32 /\ kk == vkk} *)
(*   -> nn:size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} -> *)
(*   Stack unit *)
(*     (requires (fun h -> live h output /\ live h d /\ live h k *)
(*                    /\ disjoint output d /\ disjoint d output *)
(*                    /\ disjoint output k /\ disjoint k output)) *)
(*     (ensures  (fun h0 _ h1 -> preserves_live h0 h1 /\ modifies1 output h0 h1 *)
(*                          /\ h1.[output] == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn))) *)

(* let blake2s #vll #vkk #vnn output d ll k kk nn = *)
(*   let h0 = ST.get () in *)
(*   mkstate #h0 output *)
(*   (fun h -> (fun _ sv -> sv == Spec.Blake2s.blake2s (v ll) h0.[d] (v kk) h0.[k] (v nn))) *)
(*   (fun st -> *)
(*     let fk = if kk =. (size 0) then false else true in *)
(*     let rem = ll %. (size Spec.size_block) in *)
(*     let nblocks = ll /. (size Spec.size_block) in *)
(*     let blocks = sub #_ #_ #(v nblocks * Spec.size_block) d (size 0) (nblocks *. (size Spec.size_block)) in *)
(*     let last = sub #_ #_ #(v rem) d (nblocks *. (size Spec.size_block)) rem in *)
(*     blake2s_init #vkk st k kk nn; *)
(*     if ll =. (size 0) && kk =. (size 0) then blake2s_update_last_empty st *)
(*     else begin *)
(*       let nprev = if kk =. (size 0) then (size 0) else (size 1) in *)
(*       blake2s_update_multi st nprev nblocks d; *)
(*       blake2s_update_last #rem st ll last rem fk *)
(*     end; *)
(*     blake2s_finish #vnn output st nn *)
(*   ) *)

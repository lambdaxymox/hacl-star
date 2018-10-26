module Hacl.Impl.Blake2s

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators

module ST = FStar.HyperStack.ST
module Seq = Lib.Sequence
module Loops = Lib.LoopCombinators
module Spec = Spec.Blake2

(* Alias types from Specification *)
type alg = Spec.alg
type word_t a = Spec.word_t a
type limb_t a = Spec.limb_t a

(* Define algorithm parameters *)
type vector_wp (a:alg) = lbuffer (word_t a) Spec.size_block_w
type block_wp (a:alg) = lbuffer (word_t a) Spec.size_block_w
type block_p (a:alg) = lbuffer uint8 (Spec.size_block a)
type hash_wp (a:alg) = lbuffer (word_t a) Spec.size_hash_w
type index_t = n:size_t{size_v n < 16}

inline_for_extraction let size_word (a:alg) = size (Spec.size_word a)
inline_for_extraction let size_block (a:alg) : n:size_t{v n > 0 /\ v n == Spec.size_block a} =
  (size Spec.size_block_w) *. (size_word a)


/// Constants

let const_iv = icreateL_global Spec.list_iv_S
let const_sigma = icreateL_global Spec.list_sigma
let rTable_S = icreateL_global Spec.rTable_list_S

/// Accessors for constants

val get_iv:
    p:alg
  -> s:size_t{size_v s < 8} ->
  Stack (word_t p)
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\
      uint_v z == uint_v (Seq.index (Spec.ivTable p) (size_v s))))

[@ Substitute ]
let get_iv p s =
  recall_contents const_iv (Spec.ivTable p);
  let r = iindex const_iv s in
  secret r


#set-options "--z3rlimit 50"
[@ Substitute ]
val set_iv:
    p:alg
  -> hash:hash_wp p ->
  Stack unit
    (requires (fun h -> live h hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Seq.map secret (Spec.ivTable p)))
[@ Substitute ]
let set_iv a hash =
  recall_contents const_iv (Spec.ivTable a);
  let h0 = ST.get() in
  imapT hash (size (Spec.size_hash_w)) secret const_iv


#set-options "--z3rlimit 15"

val set_iv_sub:
    p:alg
  -> b:lbuffer (word_t p) 16 ->
  Stack unit
    (requires (fun h -> live h b))
    (ensures  (fun h0 _ h1 -> modifies1 b h0 h1
                      /\ (let b0: Seq.lseq (word_t p) 16 = h0.[b] in
                         let b1: Seq.lseq (word_t p) 16 = h1.[b] in
                         let src = Seq.map secret (Spec.ivTable p) in
                         b1 == Seq.update_sub #(word_t p) #16 b0 8 8 src)))
[@ Substitute ]
let set_iv_sub p b =
  let h0 = ST.get () in
  let half0 = sub #(word_t p) #16 #8 b (size 0) (size 8) in
  let half1 = sub #(word_t p) #16 #8 b (size 8) (size 8) in
  let h1 = ST.get () in
  set_iv p half1;
  let h2 = ST.get () in
  Seq.eq_intro h2.[b] (Seq.concat #(word_t p) #8 #8 h2.[half0] h2.[half1]);
  Seq.eq_intro h2.[b] (Seq.update_sub #(word_t p) #16 h0.[b] 8 8 (Seq.map secret (Spec.ivTable p)))


#reset-options

val get_sigma:
  s:size_t{size_v s < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.const_sigma (size_v s))))

[@ Substitute ]
let get_sigma s =
  recall_contents const_sigma Spec.const_sigma;
  iindex const_sigma s


#set-options "--z3rlimit 15"

val get_sigma_sub:
  start:size_t ->
  i:size_t{v i < 16 /\ v start + v i < 160} ->
  Stack Spec.sigma_elt_t
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index Spec.const_sigma (v start + v i))))

[@ Substitute ]
let get_sigma_sub start i = get_sigma (start +. i)


#reset-options

val get_r:
    p:alg
  -> s:size_t{size_v s < 4} ->
  Stack (rotval U32)
    (requires (fun h -> True))
    (ensures  (fun h0 z h1 -> h0 == h1 /\ v z == v (Seq.index (Spec.rTable p) (v s))))

[@ Substitute ]
let get_r a s =
  recall_contents rTable_S (Spec.rTable Spec.Blake2S);
  iindex rTable_S s


/// Define algorithm functions

val g1: p:alg -> wv:vector_wp p -> a:index_t -> b:index_t -> r:rotval U32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g1 p h0.[wv] (v a) (v b) r))

let g1 al wv a b r =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- (wv_a ^. wv_b) >>>. r


val g2: p:alg -> wv:vector_wp p -> a:index_t -> b:index_t -> x:uint32 ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.g2 p h0.[wv] (v a) (v b) x))

let g2 al wv a b x =
  let wv_a = wv.(a) in
  let wv_b = wv.(b) in
  wv.(a) <- add_mod #U32 (wv_a +. wv_b) x


val blake2_mixing : p:alg -> wv:vector_wp p -> a:index_t -> b:index_t -> c:index_t -> d:index_t -> x:word_t p -> y:word_t p ->
  Stack unit
    (requires (fun h -> live h wv))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_mixing p h0.[wv] (v a) (v b) (v c) (v d) x y))

let blake2_mixing p wv a b c d x y =
  let r0 = get_r p (size 0) in
  let r1 = get_r p (size 1) in
  let r2 = get_r p (size 2) in
  let r3 = get_r p (size 3) in
  g2 p wv a b x;
  g1 p wv d a r0;
  g2 p wv c d (u32 0);
  g1 p wv b c r1;
  g2 p wv a b y;
  g1 p wv d a r2;
  g2 p wv c d (u32 0);
  g1 p wv b c r3


#set-options "--z3rlimit 15"

val blake2_round1 : p:alg -> wv:vector_wp p -> m:block_wp p -> i:size_t{size_v i <= 9} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                  /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round1 p h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round1 p wv m i =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s0 = get_sigma_sub start_idx (size 0) in
  let s1 = get_sigma_sub start_idx (size 1) in
  let s2 = get_sigma_sub start_idx (size 2) in
  let s3 = get_sigma_sub start_idx (size 3) in
  let s4 = get_sigma_sub start_idx (size 4) in
  let s5 = get_sigma_sub start_idx (size 5) in
  let s6 = get_sigma_sub start_idx (size 6) in
  let s7 = get_sigma_sub start_idx (size 7) in
  blake2_mixing p wv (size 0) (size 4) (size  8) (size 12) m.(s0) m.(s1);
  blake2_mixing p wv (size 1) (size 5) (size  9) (size 13) m.(s2) m.(s3);
  blake2_mixing p wv (size 2) (size 6) (size 10) (size 14) m.(s4) m.(s5);
  blake2_mixing p wv (size 3) (size 7) (size 11) (size 15) m.(s6) m.(s7)


#set-options "--z3rlimit 15"

val blake2_round2 : p: alg -> wv:vector_wp p -> m:block_wp p -> i:size_t{size_v i <= 9} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                  /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round2 p h0.[wv] h0.[m] (v i)))

[@ Substitute ]
let blake2_round2 p wv m i =
  let start_idx = (i %. (size 10)) *. (size 16) in
  let s8 = get_sigma_sub start_idx (size 8) in
  let s9 = get_sigma_sub start_idx (size 9) in
  let s10 = get_sigma_sub start_idx (size 10) in
  let s11 = get_sigma_sub start_idx (size 11) in
  let s12 = get_sigma_sub start_idx (size 12) in
  let s13 = get_sigma_sub start_idx (size 13) in
  let s14 = get_sigma_sub start_idx (size 14) in
  let s15 = get_sigma_sub start_idx (size 15) in
  blake2_mixing p wv (size 0) (size 5) (size 10) (size 15) m.(s8) m.(s9);
  blake2_mixing p wv (size 1) (size 6) (size 11) (size 12) m.(s10) m.(s11);
  blake2_mixing p wv (size 2) (size 7) (size  8) (size 13) m.(s12) m.(s13);
  blake2_mixing p wv (size 3) (size 4) (size  9) (size 14) m.(s14) m.(s15)


#reset-options

val blake2_round : p:alg -> wv:vector_wp p -> m:block_wp p -> i:size_t{v i <= 9} ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m
                   /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_round p h0.[m] (v i) h0.[wv]))

let blake2_round p wv m i =
  blake2_round1 p wv m i;
  blake2_round2 p wv m i


#reset-options "--z3rlimit 15"

val blake2_compress1:
    p:alg
  -> wv:vector_wp p
  -> s:hash_wp p
  -> m:block_wp p
  -> offset:limb_t p
  -> flag:bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m /\ live h wv
                     /\ disjoint wv s /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress1 p h0.[wv] h0.[s] h0.[m] offset flag))

[@ Substitute ]
let blake2_compress1 p wv s m offset flag =
  update_sub wv (size 0) (size 8) s;
  set_iv_sub p wv;
  let low_offset = Spec.limb_to_word p offset in
  let high_offset = Spec.limb_to_word p (offset >>. size 32) in
  let wv_12 = logxor wv.(size 12) low_offset in
  let wv_13 = logxor wv.(size 13) high_offset in
  let wv_14 = logxor wv.(size 14) (ones (Spec.wt p) SEC) in
  wv.(size 12) <- wv_12;
  wv.(size 13) <- wv_13;
 (if flag then wv.(size 14) <- wv_14)


#reset-options "--z3rlimit 25"

val blake2_compress2 :
    p: alg
  -> wv:vector_wp p
  -> m:block_wp p ->
  Stack unit
    (requires (fun h -> live h wv /\ live h m /\ disjoint wv m))
    (ensures  (fun h0 _ h1 -> modifies1 wv h0 h1
                         /\ h1.[wv] == Spec.blake2_compress2 p h0.[wv] h0.[m]))

[@ Substitute ]
let blake2_compress2 p wv m =
  let h0 = ST.get () in
  [@inline_let]
  let spec h = Spec.blake2_round p h.[m] in
  loop1 h0 (size (Spec.rounds p)) wv spec
  (fun i ->
    Loops.unfold_repeati (Spec.rounds p) (spec h0) (as_seq h0 wv) (v i);
    blake2_round p wv m i)


#reset-options "--z3rlimit 15"

val blake2_compress3_inner :
    p:alg
  -> wv:vector_wp p
  -> i:size_t{size_v i < 8}
  -> s:hash_wp p ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                   /\ disjoint s wv /\ disjoint wv s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3_inner p h0.[wv] (v i) h0.[s]))

[@ Substitute ]
let blake2_compress3_inner p wv i s =
  let i_plus_8 = i +. (size 8) in
  let hi_xor_wvi = s.(i) ^. wv.(i) in
  let hi = logxor #(Spec.wt p) hi_xor_wvi wv.(i_plus_8) in
  s.(i) <- hi


#reset-options "--z3rlimit 25"

val blake2_compress3 :
    p:alg
  -> wv:vector_wp p
  -> s:hash_wp p ->
  Stack unit
    (requires (fun h -> live h s /\ live h wv
                     /\ disjoint wv s /\ disjoint s wv))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress3 p h0.[wv] h0.[s]))

[@ Substitute ]
let blake2_compress3 p wv s =
  [@inline_let]
  let spec h = Spec.blake2_compress3_inner p h.[wv] in
  let h0 = ST.get () in
  loop1 h0 (size 8) s
    (fun h -> spec h)
    (fun i ->
      Loops.unfold_repeati 8 (spec h0) (as_seq h0 s) (v i);
      blake2_compress3_inner p wv i s)


#reset-options "--z3rlimit 15"

val blake2_compress :
    p:alg
  -> s:hash_wp p
  -> m:block_wp p
  -> offset:limb_t p
  -> flag:bool ->
  Stack unit
    (requires (fun h -> live h s /\ live h m
                     /\ disjoint s m /\ disjoint m s))
    (ensures  (fun h0 _ h1 -> modifies1 s h0 h1
                         /\ h1.[s] == Spec.blake2_compress p h0.[s] h0.[m] offset flag))

let blake2_compress p s m offset flag =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = h1.[s] == Spec.blake2_compress p h0.[s] h0.[m] offset flag in
  salloc1_trivial h0 (size 16) (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer s)) spec
  (fun wv ->
    blake2_compress1 p wv s m offset flag;
    blake2_compress2 p wv m;
    blake2_compress3 p wv s)


#reset-options "--z3rlimit 15"

val blake2_update_block:
    p: alg
  -> hash:hash_wp p
  -> prev:limb_t p
  -> d:block_p p ->
  Stack unit
    (requires (fun h -> live h hash /\ live h d /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.blake2_update_block p (uint_v prev) h0.[d] h0.[hash]))

let blake2_update_block p hash prev d =
  let h0 = ST.get () in
  [@inline_let]
  let spec _ h1 = h1.[hash] == Spec.blake2_update_block p (uint_v prev) h0.[d] h0.[hash] in
  salloc1_trivial h0 (size 16) (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer hash)) spec
  (fun block_w ->
     uints_from_bytes_le block_w (size Spec.size_block_w) d;
     let offset = prev in
     blake2_compress p hash block_w offset false)


#reset-options

val blake2_init_hash:
    p:alg
  -> hash:hash_wp p
  -> kk:size_t{v kk <= 32}
  -> nn:size_t{1 <= v nn /\ v nn <= Spec.max_output p} ->
  Stack unit
     (requires (fun h -> live h hash))
     (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                          /\ h1.[hash] == Spec.blake2_init_hash p (v kk) (v nn)))
[@ Substitute]
let blake2_init_hash p hash kk nn =
  set_iv p hash;
  let s0 = hash.(size 0) in
  let kk_shift_8 = shift_left #U32 (size_to_uint32 kk) (size 8) in
  let s0' = s0 ^. (Spec.nat_to_word p 0x01010000) ^. kk_shift_8 ^. size_to_uint32 nn in
  hash.(size 0) <- s0'


#reset-options "--z3rlimit 15"

val blake2_init_branching:
    #vkk:size_t
  -> p:alg
  -> hash:hash_wp p
  -> key_block:lbuffer uint8 64
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= Spec.max_output p} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h k /\ live h key_block
                   /\ disjoint hash k /\ disjoint hash key_block /\ disjoint key_block k))
    (ensures  (fun h0 _ h1 -> modifies2 hash key_block h0 h1
                    /\ (if (v kk) = 0 then h1.[hash] == h0.[hash] else
                       let key_block1 = Seq.update_sub #uint8 #64 h0.[key_block] 0 (v kk) h0.[k] in
                       h1.[hash] == Spec.blake2_update_block p (Spec.size_block p) key_block1 h0.[hash])))

[@ Substitute ]
let blake2_init_branching #vkk p hash key_block k kk nn =
  let h0 = ST.get () in
  if kk <>. (size 0) then
  begin
    update_sub key_block (size 0) kk k;
    let prev = Spec.word_to_limb p (secret (size_block p)) in
    blake2_update_block p hash prev key_block
  end


#reset-options "--z3rlimit 15"

val blake2_init:
    #vkk:size_t
  -> p:alg
  -> hash:hash_wp p
  -> k:lbuffer uint8 (v vkk)
  -> kk:size_t{v kk <= 32 /\ kk == vkk}
  -> nn:size_t{1 <= v nn /\ v nn <= Spec.max_output p} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h k
                   /\ disjoint hash k /\ disjoint k hash))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_init p (v kk) h0.[k] (v nn)))

[@ Substitute ]
let blake2_init #vkk p hash k kk nn =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 64) (u8 0) (Ghost.hide (LowStar.Buffer.loc_buffer hash))
  (fun _ h1 -> h1.[hash] == Spec.blake2_init p (size_v kk) h0.[k] (v nn))
  (fun key_block ->
    blake2_init_hash p hash kk nn;
    blake2_init_branching #vkk p hash key_block k kk nn)


#reset-options "--z3rlimit 15"

val blake2_update_last:
    #vlen: size_t
  -> p: alg
  -> hash: hash_wp p
  -> prev: limb_t p
  -> last: lbuffer uint8 (v vlen)
  -> len: size_t{v len <= Spec.size_block p /\ len == vlen} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h last /\ disjoint hash last))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.Blake2.blake2_update_last p (uint_v prev) (v len) h0.[last] h0.[hash]))

let blake2_update_last #vlen p hash prev last len =
  push_frame ();
  let last_block = create #uint8 (size 64) (u8 0) in
  let last_block_w = create #(word_t p) (size 16) (Spec.nat_to_word p 0) in
  update_sub #(word_t p) #16 #(v vlen) last_block (size 0) len last;
  uints_from_bytes_le #(Spec.wt p) #SEC #16 last_block_w (size 16) last_block;
  let offset = prev in
  blake2_compress p hash last_block_w offset true;
  pop_frame ()


#reset-options "--z3rlimit 15"

val blake2_finish:
    #vnn: size_t
  -> p: alg
  -> output: lbuffer uint8 (v vnn)
  -> hash: hash_wp p
  -> nn: size_t{1 <= v nn /\ v nn <= 32 /\ nn == vnn} ->
  Stack unit
    (requires (fun h -> live h hash
                   /\ live h output /\ disjoint output hash /\ disjoint hash output))
    (ensures  (fun h0 _ h1 -> modifies1 output h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2_finish p h0.[hash] (v nn)))

let blake2_finish #vnn p output hash nn =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 32) (u8 0) (Ghost.hide (LowStar.Buffer.loc_buffer output))
  (fun _ h1 -> h1.[output] == Spec.Blake2.blake2_finish p h0.[hash] (v nn))
  (fun full ->
    uints_to_bytes_le full (size 8) hash;
    let final = sub full (size 0) nn in
    copy output nn final)


#reset-options "--z3rlimit 50"

noextract inline_for_extraction
let spec_prev1 (p:alg) (klen:size_nat{klen == 0 \/ klen == 1})
	      (dlen:size_nat{if klen = 0 then dlen < Spec.max_limb p else dlen + Spec.size_block p < Spec.max_limb p})
	      (i:size_nat{i < dlen / (Spec.size_block p)}) : r:nat{r < Spec.max_limb p} = (klen + i + 1) * Spec.size_block p

noextract inline_for_extraction
let spec_prev2 (p:alg) (klen:size_nat{klen == 0 \/ klen == 1})
	      (dlen:size_nat{if klen = 0 then dlen < Spec.max_limb p else dlen + Spec.size_block p < Spec.max_limb p})
	      (i:size_nat{i == dlen / (Spec.size_block p)}) : r:nat{r < Spec.max_limb p} = (klen * (Spec.size_block p)) + dlen


noextract inline_for_extraction
let prev1 (p:alg) (klen:size_t{v klen == 0 \/ v klen == 1})
          (dlen:size_t{if v klen = 0 then v dlen < Spec.max_limb p else v dlen + Spec.size_block p < Spec.max_limb p})
	  (i:size_t{v i < v dlen / (Spec.size_block p)}) :
	  (prev:uint64{uint_v prev == spec_prev1 p (v klen) (v dlen) (v i)})
	  = let p = Spec.Blake2.word_to_limb p (klen +. i +. size 1) *. Spec.nat_to_limb p 64 in
	    assert (uint_v p == spec_prev1 p (v klen) (v dlen) (v i));
	    p

noextract inline_for_extraction
let prev2 (p:alg) (klen:size_t{v klen == 0 \/ v klen == 1})
          (dlen:size_t{if v klen = 0 then v dlen < Spec.max_limb p else v dlen + Spec.size_block p < Spec.max_limb p})
	  (i:size_t{v i == v dlen / (Spec.size_block p)}) :
	  (prev:uint64{uint_v prev == spec_prev2 p (v klen) (v dlen) (v i)})
	  = Spec.word_to_limb p dlen +. Spec.word_to_limb p (klen *. size 64)


#reset-options "--z3rlimit 150"

inline_for_extraction
val blake2_update:
    #vll: size_t
  -> p: alg
  -> hash: hash_wp p
  -> d: lbuffer uint8 (v vll)
  -> ll: size_t{v ll == v vll}
  -> kk: size_t{v kk <= 32 /\ (if v kk = 0 then v ll < Spec.max_limb p else v ll + Spec.size_block p < Spec.max_limb p)} ->
  Stack unit
    (requires (fun h -> live h hash /\ live h d /\ disjoint hash d))
    (ensures  (fun h0 _ h1 -> modifies1 hash h0 h1
                         /\ h1.[hash] == Spec.blake2_update p h0.[hash] h0.[d] (v kk)))

let blake2_update #vll p hash d ll kk =
  let h0 = ST.get() in
  let klen = if kk =. size 0 then size 0 else size 1 in
  loopi_blocks (size_block p) ll d
    (Spec.spec_update_block p ((v klen + 1) * (Spec.size_block p)))
    (Spec.spec_update_last p (v klen * (Spec.size_block p) + v ll))
    (fun i block hash -> blake2_update_block p hash (prev1 p klen ll i) block)
    (fun i len last hash -> blake2_update_last #(ll %. size (Spec.size_block p)) p hash (prev2 klen ll i) last len)
    hash


#reset-options "--z3rlimit 25"

val blake2s:
    output: buffer uint8
  -> d: buffer uint8
  -> ll: size_t{length d == v ll}
  -> k: buffer uint8
  -> kk: size_t{length k == v kk /\ v kk <= 32 /\ (if v kk = 0 then v ll < pow2 64 else v ll + 64 < pow2 64)}
  -> nn:size_t{v nn == length output /\ 1 <= v nn /\ v nn <= 32} ->
  Stack unit
    (requires (fun h -> LowStar.Buffer.live h output
                   /\ LowStar.Buffer.live h d
                   /\ LowStar.Buffer.live h k
                   /\ LowStar.Buffer.disjoint output d
                   /\ LowStar.Buffer.disjoint output k))
    (ensures  (fun h0 _ h1 -> LowStar.Buffer.modifies (LowStar.Buffer.loc_buffer output) h0 h1
                         /\ h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn)))

let blake2s output d ll k kk nn =
  let h0 = ST.get () in
  salloc1_trivial h0 (size 8) (u32 0) (Ghost.hide (LowStar.Buffer.loc_buffer output))
  (fun _ h1 -> h1.[output] == Spec.Blake2.blake2s h0.[d] (v kk) h0.[k] (v nn))
  (fun hash ->
    blake2_init #kk Spec.Blake2S hash k kk nn;
    blake2_update #ll Spec.Blake2S hash d ll kk;
    blake2_finish #nn Spec.Blake2S output hash nn)

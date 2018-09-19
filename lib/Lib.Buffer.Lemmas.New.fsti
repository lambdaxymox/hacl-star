module Lib.Buffer.Lemmas.New


/// ``unused_in b h`` holds only if buffer ``b`` has not been allocated
/// yet.

val unused_in (#a: Type) (b: buffer a) (h: HS.mem) : GTot Type0
/// A live buffer has already been allocated.

val live_not_unused_in (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)

(* FIXME: the following definition is necessary to isolate the pattern
   because of unification. In other words, if we attached the pattern
   to `live_not_unused_in`, then we would not be able to use
   `FStar.Classical.forall_intro_`n and
   `FStar.Classical.move_requires` due to unification issues.  Anyway,
   we plan to isolate patterns in a separate module to clean up the Z3
   context.
 *)

let live_not_unused_in' (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b /\ b `unused_in` h))
  (ensures False)
  [SMTPat (live h b); SMTPat (b `unused_in` h)]
= live_not_unused_in h b

/// Buffers live in the HyperStack model, which is an extension of
/// the HyperHeap model, a hierarchical memory model that divides the
/// heap into a tree of regions. This coarse-grained separation
/// allows the programmer to state modifies clauses at the level of
/// regions, rather than on individual buffers.
///
/// The HyperHeap memory model is described:
///  - in the 2016 POPL paper: https://www.fstar-lang.org/papers/mumon/
///  - in the relevant section of the F* tutorial: http://www.fstar-lang.org/tutorial/
///
/// ``frameOf b`` returns the identifier of the region in which the
/// buffer ``b`` lives.

val frameOf (#a: Type) (b: buffer a) : GTot HS.rid


/// ``as_addr b`` returns the abstract address of the buffer in its
/// region, as an allocation unit: two buffers that are allocated
/// separately in the same region will actually have different
/// addresses, but a sub-buffer of a buffer will actually have the
/// same address as its enclosing buffer.

val as_addr (#a: Type) (b: buffer a) : GTot nat


/// A buffer is unused if, and only if, its address is unused.

val unused_in_equiv (#a: Type) (b: buffer a) (h: HS.mem) : Lemma
  (ensures (unused_in b h <==> (HS.live_region h (frameOf b) ==> as_addr b `Heap.addr_unused_in` (Map.sel (HS.get_hmap h) (frameOf b)))))


/// If a buffer is live, then so is its region.

val live_region_frameOf (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (requires (live h b))
  (ensures (HS.live_region h (frameOf b)))
  [SMTPatOr [
    [SMTPat (live h b)];
    [SMTPat (HS.live_region h (frameOf b))];
  ]]


/// The contents of a buffer ``b`` has the same length as ``b`` itself.

val length_as_seq (#a: Type) (h: HS.mem) (b: buffer a) : Lemma
  (Seq.length (as_seq h b) == length b)
  [SMTPat (Seq.length (as_seq h b))]


/// ``get`` is an often-convenient shorthand to index the value of a
/// given buffer in a given heap, for proof purposes.

let get (#a: Type) (h: HS.mem) (p: buffer a) (i: nat) : Ghost a
  (requires (i < length p))
  (ensures (fun _ -> True))
= Seq.index #a #(length p) (as_seq h p) i


/// A buffer ``smaller`` is included in another buffer ``larger``, denoted
/// as ``includes larger smaller``, if ``smaller`` is a sub-buffer of
/// ``larger``. (See ``gsub`` below for how to actually construct such a
/// sub-buffer of a buffer.)

val includes (#a: Type) (larger smaller: buffer a) : GTot Type0


/// The liveness of a sub-buffer is exactly equivalent to the liveness
/// of its enclosing buffer.

val includes_live (#a: Type) (h: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (live h larger <==> live h smaller))
  [SMTPatOr [
    [SMTPat (includes larger smaller); SMTPat (live h larger)];
    [SMTPat (includes larger smaller); SMTPat (live h smaller)];
  ]]


/// If the contents of a buffer are equal in two given heaps, then so
/// are the contents of any of its sub-buffers.

val includes_as_seq (#a: Type) (h1 h2: HS.mem) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller /\ as_seq h1 larger == as_seq h2 larger))
  (ensures (as_seq h1 smaller == as_seq h2 smaller))


/// Inclusion is a preorder.

val includes_refl (#a: Type) (x: buffer a) : Lemma
  (includes x x)
  [SMTPat (includes x x)]

val includes_trans (#a: Type) (x y z: buffer a) : Lemma
  (requires (x `includes` y /\ y `includes` z))
  (ensures (x `includes` z))
  [SMTPatOr [
    [SMTPat (x `includes` y); SMTPat (y `includes` z)];
    [SMTPat (x `includes` y); SMTPat (x `includes` z)];
    [SMTPat (y `includes` z); SMTPat (x `includes` z)];
  ]]


/// A buffer and any of its sub-buffers live in the same region, and
/// at the same address, and are either both null or both not null.

val includes_frameOf_as_addr (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (frameOf larger == frameOf smaller /\ as_addr larger == as_addr smaller))
  [SMTPat (larger `includes` smaller)]



/// A buffer is live exactly at the same time as all of its sub-buffers.

val live_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: size_t) (n: size_t) : Lemma
  (requires (v i + v n <= length b))
  (ensures (live h (gsub b i n) <==> live h b))
  [SMTPat (live h (gsub b i n))]


/// A sub-buffer is included in its enclosing buffer.

val includes_gsub (#a: Type) (b: buffer a) (i: size_t) (n: size_t) : Lemma
  (requires (v i + v n <= length b))
  (ensures (b `includes` gsub b i n))
  [SMTPat (gsub b i n)]


/// The length of a sub-buffer is exactly the one provided at ``gsub``.

val len_gsub (#a: Type) (b: buffer a) (i: size_t) (n: size_t) : Lemma
  (requires (v i + v n <= length b))
  (ensures (len (gsub b i n) == n))
  [SMTPatOr [
    [SMTPat (len (gsub b i n))];
    [SMTPat (length (gsub b i n))];
  ]]


/// Nesting two ``gsub`` collapses into one ``gsub``, transitively.

val gsub_gsub (#a: Type) (b: buffer a) (i1: size_t) (len1: size_t) (i2: size_t) (len2: size_t) : Lemma
  (requires (v i1 + v len1 <= length b /\ v i2 + v len2 <= v len1))
  (ensures (
    v i1 + v len1 <= length b /\ v i2 + v len2 <= v len1 /\
    gsub (gsub b i1 len1) i2 len2 == gsub b (Int.add i1 i2) len2
  ))
  [SMTPat (gsub (gsub b i1 len1) i2 len2)]


/// A buffer ``b`` is equal to its "largest" sub-buffer, at index 0 and
/// length ``len b``.

val gsub_zero_length (#a: Type) (b: buffer a) : Lemma
  (b == gsub b (Int.size 0) (len b))


/// The contents of a sub-buffer is the corresponding slice of the
/// contents of its enclosing buffer.

val as_seq_gsub (#a: Type) (h: HS.mem) (b: buffer a) (i: size_t) (len: size_t) : Lemma
  (requires (v i + v len <= length b))
  (ensures (as_seq h (gsub b i len) == Seq.slice #a #(length b) (as_seq h b) (v i) (v i + v len)))
  [SMTPat (as_seq h (gsub b i len))]


/// Disjointness is symmetric.

val disjoint_sym (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : Lemma
  (disjoint b1 b2 <==> disjoint b2 b1)
  [SMTPat (disjoint b1 b2)]


/// If two buffers are disjoint, then so are any of their sub-buffers.

val disjoint_includes_l (#a1 #a2: Type) (b1 b1' : buffer a1) (b2: buffer a2) : Lemma
  (requires (includes b1 b1' /\ disjoint b1 b2))
  (ensures (disjoint b1' b2))
  [SMTPat (disjoint b1' b2); SMTPat (includes b1 b1')]

val disjoint_includes_r (#a1 #a2: Type) (b1 : buffer a1) (b2 b2': buffer a2) : Lemma
  (requires (includes b2 b2' /\ disjoint b1 b2))
  (ensures (disjoint b1 b2'))
  [SMTPat (disjoint b1 b2'); SMTPat (includes b2 b2')]


/// A buffer that has not been allocated yet is disjoint from all
/// buffers that are already currently allocated. Consequently, two
/// buffers that are allocated separately are disjoint.

val live_unused_in_disjoint (#a1 #a2: Type) (h: HS.mem) (b1: buffer a1) (b2: buffer a2) : Lemma
  (requires (live h b1 /\ (unused_in b2 h)))
  (ensures (disjoint b1 b2))
  [SMTPatOr [
    [SMTPat (live h b1); SMTPat (disjoint b1 b2)];
    [SMTPat (live h b1); SMTPat (unused_in b2 h)];
    [SMTPat (unused_in b2 h); SMTPat (disjoint b1 b2)];
  ]]

/// If two buffers live in different regions or at different
/// addresses, then they are disjoint.

val as_addr_disjoint (#a1 #a2: Type) (b1: buffer a1) (b2: buffer a2) : Lemma
  (requires (frameOf b1 <> frameOf b2 \/ as_addr b1 <> as_addr b2))
  (ensures (disjoint b1 b2))
  [SMTPatOr [
    [SMTPat (disjoint b1 b2)];
    [SMTPat (frameOf b1); SMTPat (frameOf b2)];
    [SMTPat (as_addr b1); SMTPat (as_addr b2)];
  ]]


/// If two buffers span disjoint ranges from a common enclosing
/// buffer, then they are disjoint.

val gsub_disjoint (#a: Type) (b: buffer a) (i1 len1 i2 len2: size_t) : Lemma
  (requires (
    v i1 + v len1 <= length b /\
    v i2 + v len2 <= length b /\
    (v i1 + v len1 <= v i2 \/ v i2 + v len2 <= v i1)
  ))
  (ensures (disjoint (gsub b i1 len1) (gsub b i2 len2)))
  [SMTPat (disjoint (gsub b i1 len1) (gsub b i2 len2))]



/// Two pointers having different contents are disjoint. This is valid
/// only for pointers, i.e. buffers of size 1.

val pointer_distinct_sel_disjoint
  (#a: Type)
  (b1: pointer a)
  (b2: pointer a)
  (h: HS.mem)
: Lemma
  (requires (
    live h b1 /\
    live h b2 /\
    get h b1 0 =!= get h b2 0
  ))
  (ensures (
    disjoint b1 b2
  ))


/// The following definitions are needed to implement the generic
/// modifies clause. Those should not be used in client code. They
/// appear in the interface only because the modifies clause is
/// defined in another module, ``LowStar.Modifies``.

val abuffer' (region: HS.rid) (addr: nat) : Tot Type0

inline_for_extraction
let abuffer (region: HS.rid) (addr: nat) : Tot Type0 = Ghost.erased (abuffer' region addr)

val abuffer_preserved (#r: HS.rid) (#a: nat) (b: abuffer r a) (h h' : HS.mem) : GTot Type0

val abuffer_preserved_refl (#r: HS.rid) (#a: nat) (b: abuffer r a) (h : HS.mem) : Lemma
  (abuffer_preserved b h h)

val abuffer_preserved_trans (#r: HS.rid) (#a: nat) (b: abuffer r a) (h1 h2 h3 : HS.mem) : Lemma
  (requires (abuffer_preserved b h1 h2 /\ abuffer_preserved b h2 h3))
  (ensures (abuffer_preserved b h1 h3))

val same_mreference_abuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
  (f: (
    (a' : Type) ->
    (pre: Preorder.preorder a') ->
    (r': HS.mreference a' pre) ->
    Lemma
    (requires (h1 `HS.contains` r' /\ r == HS.frameOf r' /\ a == HS.as_addr r'))
    (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))
  ))
: Lemma
  (abuffer_preserved b h1 h2)

val addr_unused_in_abuffer_preserved
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (HS.live_region h1 r ==> a `Heap.addr_unused_in` (Map.sel (HS.get_hmap h1) r)))
  (ensures (abuffer_preserved b h1 h2))

val abuffer_of_buffer (#t: Type) (b: buffer t) : Tot (abuffer (frameOf b) (as_addr b))

val abuffer_preserved_elim (#t: Type) (b: buffer t) (h h' : HS.mem) : Lemma
  (requires (abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h' /\ live h b))
  (ensures (live h' b /\ as_seq h b == as_seq h' b))

let unused_in_abuffer_preserved
  (#t: Type)
  (b: buffer t)
  (h h' : HS.mem)
: Lemma
  (requires (b `unused_in` h))
  (ensures (abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h'))
= Classical.move_requires (fun b -> live_not_unused_in #t h b) b;
  //live_null t h;
  //null_unique b;
  unused_in_equiv b h;
  addr_unused_in_abuffer_preserved #(frameOf b) #(as_addr b) (abuffer_of_buffer b) h h'

val abuffer_includes (#r: HS.rid) (#a: nat) (larger smaller: abuffer r a) : GTot Type0

val abuffer_includes_refl (#r: HS.rid) (#a: nat) (b: abuffer r a) : Lemma
  (b `abuffer_includes` b)

val abuffer_includes_trans (#r: HS.rid) (#a: nat) (b1 b2 b3: abuffer r a) : Lemma
  (requires (b1 `abuffer_includes` b2 /\ b2 `abuffer_includes` b3))
  (ensures (b1 `abuffer_includes` b3))

val abuffer_includes_abuffer_preserved (#r: HS.rid) (#a: nat) (larger smaller: abuffer r a) (h1 h2: HS.mem) : Lemma
  (requires (larger `abuffer_includes` smaller /\ abuffer_preserved larger h1 h2))
  (ensures (abuffer_preserved smaller h1 h2))

val abuffer_includes_intro (#t: Type) (larger smaller: buffer t) : Lemma
  (requires (larger `includes` smaller))
  (ensures (
    let r = frameOf larger in
    let a = as_addr larger in
    abuffer_includes #r #a (abuffer_of_buffer larger) (abuffer_of_buffer smaller)
  ))

val abuffer_disjoint (#r: HS.rid) (#a: nat) (b1 b2: abuffer r a) : GTot Type0

val abuffer_disjoint_sym (#r: HS.rid) (#a: nat) (b1 b2: abuffer r a) : Lemma
  (abuffer_disjoint b1 b2 <==> abuffer_disjoint b2 b1)

val abuffer_disjoint_includes (#r: HS.rid) (#a: nat) (larger1 larger2: abuffer r a) (smaller1 smaller2: abuffer r a) : Lemma
  (requires (abuffer_disjoint larger1 larger2 /\ larger1 `abuffer_includes` smaller1 /\ larger2 `abuffer_includes` smaller2))
  (ensures (abuffer_disjoint smaller1 smaller2))

val abuffer_disjoint_intro (#t1 #t2: Type) (b1: buffer t1) (b2: buffer t2) : Lemma
  (requires (disjoint b1 b2 /\ frameOf b1 == frameOf b2 /\ as_addr b1 == as_addr b2))
  (ensures (
    let r = frameOf b1 in
    let a = as_addr b1 in
    abuffer_disjoint #r #a (abuffer_of_buffer b1) (abuffer_of_buffer b2)
  ))

val liveness_preservation_intro
  (#t: Type) (h h' : HS.mem) (b: buffer t)
  (f: (
    (t' : Type) ->
    (pre: Preorder.preorder t') ->
    (r: HS.mreference t' pre) ->
    Lemma
    (requires (HS.frameOf r == frameOf b /\ HS.as_addr r == as_addr b /\ h `HS.contains` r))
    (ensures (h' `HS.contains` r))
  ))
: Lemma
  (requires (live h b))
  (ensures (live h' b))


val modifies_0_live_region (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_0 h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_0_mreference (#a: Type) (#pre: Preorder.preorder a) (h1 h2: HS.mem) (r: HS.mreference a pre) : Lemma
  (requires (modifies_0 h1 h2 /\ h1 `HS.contains` r))
  (ensures (h2 `HS.contains` r /\ h1 `HS.sel` r == h2 `HS.sel` r))

let modifies_0_abuffer
  (#r: HS.rid)
  (#a: nat)
  (b: abuffer r a)
  (h1 h2: HS.mem)
: Lemma
  (requires (modifies_0 h1 h2))
  (ensures (abuffer_preserved b h1 h2))
= same_mreference_abuffer_preserved b h1 h2 (fun a' pre r' -> modifies_0_mreference h1 h2 r')

val modifies_0_unused_in
  (h1 h2: HS.mem)
  (r: HS.rid)
  (n: nat)
: Lemma
  (requires (
    modifies_0 h1 h2 /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)
  ))
  (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))

val modifies_1_live_region (#a: Type) (b: buffer a) (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_1 b h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_1_liveness
  (#a: Type) (b: buffer a) (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_1 b h1 h2 /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r'))

val modifies_1_unused_in
  (#t: Type)
  (b: buffer t)
  (h1 h2: HS.mem)
  (r: HS.rid)
  (n: nat)
: Lemma
  (requires (
    modifies_1 b h1 h2 /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)
  ))
  (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))

val modifies_1_mreference
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_1 b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))

val modifies_1_abuffer
  (#a: Type) (b : buffer a)
  (h1 h2: HS.mem)
  (b' : abuffer (frameOf b) (as_addr b))
: Lemma
  (requires (modifies_1 b h1 h2 /\ abuffer_disjoint #(frameOf b) #(as_addr b) (abuffer_of_buffer b) b'))
  (ensures (abuffer_preserved #(frameOf b) #(as_addr b) b' h1 h2))

val modifies_addr_of
  (#a: Type)
  (b: buffer a)
  (h1 h2: HS.mem)
: GTot Type0

val modifies_addr_of_live_region (#a: Type) (b: buffer a) (h1 h2: HS.mem) (r: HS.rid) : Lemma
  (requires (modifies_addr_of b h1 h2 /\ HS.live_region h1 r))
  (ensures (HS.live_region h2 r))

val modifies_addr_of_mreference
  (#a: Type) (b: buffer a)
  (h1 h2: HS.mem)
  (#a': Type) (#pre: Preorder.preorder a') (r' : HS.mreference a' pre)
: Lemma
  (requires (modifies_addr_of b h1 h2 /\ (frameOf b <> HS.frameOf r' \/ as_addr b <> HS.as_addr r') /\ h1 `HS.contains` r'))
  (ensures (h2 `HS.contains` r' /\ h1 `HS.sel` r' == h2 `HS.sel` r'))

val modifies_addr_of_unused_in
  (#t: Type)
  (b: buffer t)
  (h1 h2: HS.mem)
  (r: HS.rid)
  (n: nat)
: Lemma
  (requires (
    modifies_addr_of b h1 h2 /\
    (r <> frameOf b \/ n <> as_addr b) /\
    HS.live_region h1 r /\ HS.live_region h2 r /\
    n `Heap.addr_unused_in` (HS.get_hmap h2 `Map.sel` r)
  ))
  (ensures (n `Heap.addr_unused_in` (HS.get_hmap h1 `Map.sel` r)))



/// Useful shorthands for pointers, or maybe-null pointers

inline_for_extraction
type pointer (t: Type0) =
  b:buffer t { length b == 1 }

/// This is a specialization of LowStar.Buffer to non-null buffers.
///
/// Contrary to LowStar.Buffer, this module uses on Lib.IntTypes.uint32 rather than
/// UInt32.t for lengths and indices, and Lib.Sequence rather than FStar.Seq for the
/// underlying ghost representation.
///
/// The goal is to cut down the dependencies in the context on clients of this
/// module, so that neither FStar.UInt or FStar.Seq are brought into context.
///
/// Roughly, this module can be obtained by substituting in LowStar.Buffer:
///
/// FStar.Seq       -> Lib.Sequence
/// U32.t           -> Int.size_t
/// U32.v           -> Int.size_v
/// U32.add         -> Int.add
/// U32.sub         -> Int.sub
/// 0ul             -> Int.size 0
/// UInt.max_int 32 -> Int.max_size_t
///
/// and using the fact that a buffer can't be null to simplify the interface.
///
module Lib.Buffer.New

module HS  = FStar.HyperStack
module HST = FStar.HyperStack.ST

module Seq = Lib.Sequence
module Int = Lib.IntTypes

unfold
let v = Int.size_v

unfold
let size_t = Int.size_t

unfold
let size_nat = Int.size_nat

/// Low* buffers
/// ==============
///
/// The workhorse of Low*, this module allows modeling C arrays on the
/// stack and in the heap.  At compilation time, KreMLin implements
/// buffers using C arrays, i.e. if Low* type ``t`` is translated into C
/// type ``u``, then Low* type ``buffer t`` is translated to C type ``u*``.
///
/// A Hacl buffer can be empty but never NULL

val buffer (a: Type0) : Tot Type0
val lbuffer (a: Type0) (len:size_nat) : Tot Type0

/// The length of a buffer ``b`` is available as a machine integer ``len
/// b`` or as a mathematical integer ``length b``, but both in ghost
/// (proof) code only: just like in C, one cannot compute the length
/// of a buffer at run-time.

val length (#a: Type) (#len:size_nat) (b: lbuffer a len) : GTot Int.size_nat

/// ``gsub`` is the way to carve a sub-buffer out of a given
/// buffer. ``gsub b i len`` return the sub-buffer of ``b`` starting from
/// offset ``i`` within ``b``, and with length ``len``. Of course ``i`` and
/// ``len`` must fit within the length of ``b``.
///
/// ``gsub`` is the ghost version, for proof purposes. Its stateful
/// counterpart is ``sub``, see below.

val gsub (#a: Type) (#len:size_nat) (b: lbuffer a len) (i: size_nat) (n: size_nat) : Ghost (lbuffer a len)
  (requires (i + n <= length b))
  (ensures (fun y -> True))

/// ``live h b`` holds if, and only if, buffer ``b`` is currently
/// allocated in ``h`` and has not been deallocated yet.
///
/// This predicate corresponds to the C notion of "lifetime", and as
/// such, is a prerequisite for all stateful operations on buffers
/// (see below), per the C standard:
///
///   If an object is referred to outside of its lifetime, the
///   behavior is undefined.
///
///   -- ISO/IEC 9899:2011, Section 6.2.4 paragraph 2
///
/// By contrast, it is not required for the ghost versions of those
/// operators.

val live (#a: Type) (#len: size_nat) (h: HS.mem) (b: lbuffer a len) : GTot Type0

/// For functional correctness, buffers are reflected at the proof
/// level using sequences, via ``as_seq b h``, which returns the
/// contents of a given buffer ``b`` in a given heap ``h``. If ``b`` is not
/// live in ``h``, then the result is unspecified.

val as_seq (#a: Type) (#len:size_nat) (h: HS.mem) (b:lbuffer a len) : GTot (s:Seq.seq a{Seq.length #a s == len})

/// Two buffers are disjoint only if they span disjoint ranges of a
/// common enclosing buffer, or if they live in different regions or
/// at different addresses.

val disjoint (#a1 #a2: Type0) (#len1 #len2:size_nat) (b1:lbuffer a1 len1) (b2: lbuffer a2 len2) : GTot Type0

(* Basic, non-compositional modifies clauses, used only to implement the generic modifies clause. DO NOT USE in client code *)

val modifies0 (h1 h2: HS.mem) : GTot Type0

val modifies1 (#a: Type) (#len: size_nat) (b: lbuffer a len) (h1 h2: HS.mem) : GTot Type0

/// The following stateful operations on buffers do not change the
/// memory, but, as required by the C standard, they all require the
/// buffer in question to be live.

/// ``sub b i len`` constructs the sub-buffer of ``b`` starting from
/// offset ``i`` with length ``len``. KreMLin extracts this operation as
/// ``b + i`` (or, equivalently, ``&b[i]``.)

val sub (#a: Type) (#vilen #volen:size_nat) (b:lbuffer a vilen) (i: size_t) (len: size_t{v len = volen}) : HST.Stack (lbuffer a volen)
  (requires (fun h -> v i + volen <= length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b (v i) volen))

/// ``offset b i`` construct the tail of the buffer ``b`` starting from
/// offset ``i``, i.e. the sub-buffer of ``b`` starting from offset ``i``
/// with length ``U32.sub (len b) i``. KreMLin compiles it as ``b + i`` or
/// ``&b[i]``.
///
/// This stateful operation cannot be derived from ``sub``, because the
/// length cannot be computed outside of proofs.

val offset (#a: Type) (b: buffer a) (i: size_t) : HST.Stack (buffer a)
  (requires (fun h -> v i <= length b /\ live h b))
  (ensures (fun h y h' -> h == h' /\ y == gsub b i (Int.sub (len b) i)))


/// ``index b i`` reads the value of ``b`` at offset ``i`` from memory and
/// returns it. KreMLin compiles it as b[i].
val index (#a: Type) (b: buffer a) (i: size_t) : HST.Stack a
  (requires (fun h -> live h b /\ v i < length b))
  (ensures (fun h y h' -> h == h' /\ y == Seq.index #a #(length b) (as_seq #a h b) (v i)))


/// The following stateful operations on buffers modify the memory,
/// and, as usual, require the liveness of the buffer.

(* FIXME: their postconditions are using non-compositional modifies
   clauses, which are automatically converted to compositional
   modifies clauses by lemmas from LowStar.Modifies through
   patterns. In a future version, LowStar.Modifies could actually be
   merged into LowStar.Buffers so that postconditions of those
   operations would directly be specified in terms of the
   compositional modifies clauses.
 *)

/// ``g_upd_seq b s h`` updates the entire buffer `b`'s contents in
/// heap `h` to correspond to the sequence `s`
val g_upd_seq (#a:Type)
              (b:buffer a)
              (s:Seq.lseq a (length b))
              (h:HS.mem{live h b})
  : GTot HS.mem

/// A lemma specifying `g_upd_seq` in terms of its effect on the
/// buffer's underlying sequence
val g_upd_seq_as_seq (#a:Type)
                     (b:buffer a)
                     (s:Seq.lseq a (length b))
                     (h:HS.mem{live h b})
  : Lemma (let h' = g_upd_seq b s h in
           modifies_1 b h h' /\
           live h' b /\
           as_seq h' b == s)

/// ``g_upd b i v h`` updates the buffer `b` in heap `h` at location
/// `i` writing ``v`` there. This is the spec analog of the stateful
/// update `upd` below.
let g_upd (#a:Type)
          (b:buffer a)
          (i:nat{i < length b})
          (v:a)
          (h:HS.mem{live h b})
  : GTot HS.mem
  = g_upd_seq b (Seq.upd #a #(length b) (as_seq h b) i v) h

/// ``upd b i v`` writes ``v`` to the memory, at offset ``i`` of
/// buffer ``b``. KreMLin compiles it as ``b[i] = v``.
val upd
  (#a: Type)
  (b: buffer a)
  (i: size_t)
  (w: a)
: HST.Stack unit
  (requires (fun h -> live h b /\ v i < length b))
  (ensures (fun h _ h' ->
    modifies_1 b h h' /\
    live h' b /\
    as_seq h' b == Seq.upd #a #(length b) (as_seq h b) (v i) w
  ))

(* FIXME: Comment on `recall` *)

val recallable (#a: Type) (b: buffer a) : GTot Type0

val recallable_includes (#a: Type) (larger smaller: buffer a) : Lemma
  (requires (larger `includes` smaller))
  (ensures (recallable larger <==> recallable smaller))
  [SMTPatOr [
    [SMTPat (recallable larger); SMTPat (recallable smaller);];
    [SMTPat (larger `includes` smaller)];
  ]]

val recall
  (#a:Type)
  (b:buffer a)
: HST.Stack unit
  (requires (fun _ -> recallable b))
  (ensures  (fun m0 _ m1 -> m0 == m1 /\ live m1 b))


/// Deallocation. A buffer that was allocated by ``malloc`` (see below)
/// can be ``free`` d.

val freeable (#a: Type) (b: buffer a) : GTot Type0

val free
  (#a: Type)
  (b: buffer a)
: HST.ST unit
  (requires (fun h0 -> live h0 b /\ freeable b))
  (ensures (fun h0 _ h1 ->
    Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
    (HS.get_tip h1) == (HS.get_tip h0) /\
    modifies_addr_of b h0 h1 /\
    HS.live_region h1 (frameOf b)
  ))

/// Allocation. This is the common postcondition of all allocation
/// operators, which tells that the resulting buffer is fresh, and
/// specifies its initial contents.

unfold
let alloc_post_static
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
: GTot Type0
= frameOf b == r /\
  length b == len

unfold
let alloc_post_common
  (#a: Type)
  (r: HS.rid)
  (len: nat)
  (b: buffer a)
  (h0 h1: HS.mem)
: GTot Type0
= alloc_post_static r len b /\
  b `unused_in` h0 /\
  live h1 b /\
  Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
  (HS.get_tip h1) == (HS.get_tip h0) /\
  modifies_0 h0 h1

/// ``gcmalloc r init len`` allocates a memory-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer cannot be
/// freed. In fact, it is eternal: it cannot be deallocated at all.

val gcmalloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: size_t)
: HST.ST (b: buffer a {
    recallable b /\
    alloc_post_static r (v len) b
  } )
  (requires (fun h -> HST.is_eternal_region r /\ v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (v len) b h h' /\
    as_seq h' b == Seq.create (v len) init
  ))


/// ``malloc r init len`` allocates a hand-managed buffer of some
/// positive length ``len`` in an eternal region ``r``. Every cell of this
/// buffer will have initial contents ``init``. Such a buffer can be
/// freed using ``free`` above. Note that the ``freeable`` permission is
/// only on the whole buffer ``b``, and is not inherited by any of its
/// strict sub-buffers.

val malloc
  (#a: Type)
  (r: HS.rid)
  (init: a)
  (len: size_t)
: HST.ST (buffer a)
  (requires (fun h -> HST.is_eternal_region r /\ v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common r (v len) b h h' /\
    as_seq h' b == Seq.create (v len) init /\
    freeable b
  ))


/// ``alloca init len`` allocates a buffer of some positive length ``len``
/// in the current stack frame. Every cell of this buffer will have
/// initial contents ``init``. Such a buffer cannot be freed
/// individually, but is automatically freed as soon as its stack
/// frame is deallocated by ``HST.pop_frame``.

val alloca
  (#a: Type)
  (init: a)
  (len: size_t)
: HST.StackInline (buffer a)
  (requires (fun h -> v len > 0))
  (ensures (fun h b h' ->
    alloc_post_common (HS.get_tip h) (v len) b h h' /\
    as_seq h' b == Seq.create (v len) init
  ))


/// ``alloca_of_list init`` allocates a buffer in the current stack
/// frame. The initial values of the cells of this buffer are
/// specified by the ``init`` list, which must be nonempty, and of
/// length representable as a machine integer.

unfold let alloc_of_list_pre (#a: Type0) (init: list a) : GTot Type0 =
  normalize (0 < FStar.List.Tot.length init) /\
  normalize (FStar.List.Tot.length init <= Int.max_size_t)

unfold let alloc_of_list_post (#a: Type) (len: nat) (buf: buffer a) : GTot Type0 =
  normalize (length buf == len)

val alloca_of_list
  (#a: Type0)
  (init: list a)
: HST.StackInline (buffer a)
  (requires (fun h -> alloc_of_list_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    alloc_post_common (HS.get_tip h) len b h h' /\
    as_seq h' b == Seq.of_list init /\
    alloc_of_list_post #a len b
  ))

val gcmalloc_of_list
  (#a: Type0)
  (r: HS.rid)
  (init: list a)
: HST.ST (b: buffer a {
    let len = FStar.List.Tot.length init in
    recallable b /\
    alloc_post_static r len b /\
    alloc_of_list_post len b
  } )
  (requires (fun h -> HST.is_eternal_region r /\ alloc_of_list_pre #a init))
  (ensures (fun h b h' ->
    let len = FStar.List.Tot.length init in
    alloc_post_common r len b h h' /\
    as_seq h' b == Seq.of_list init
  ))


/// Additional functionality not in LowStar.Buffer


let lbuffer (a: Type0) (len: Int.size_nat) = b:buffer a{length b == len}

let gslice #a (b:buffer a) (start:size_t)
  (fin:size_t{v fin <= length b /\ v start <= v fin}) =
  gsub #a b start (Int.sub_mod fin start)

val as_lseq: #a:Type0 -> b:buffer a -> h:HS.mem -> GTot (s:Seq.lseq a (length b){s == as_seq h b})

inline_for_extraction
val slice: #a:Type0 -> b:buffer a -> start:size_t -> fin:size_t{v start <= v fin /\ v fin <= length b} ->
  HST.Stack (buffer a)
    (requires (fun h0 -> live h0 b))
    (ensures (fun h0 r h1 -> h0 == h1 /\ r == gslice #a b start fin))

inline_for_extraction
let op_Array_Assignment #a l = upd #a l

inline_for_extraction
let op_Array_Access #a l = index #a l

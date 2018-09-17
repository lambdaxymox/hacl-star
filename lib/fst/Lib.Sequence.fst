module Lib.Sequence

open FStar.Mul
open Lib.IntTypes
//open Lib.RawIntTypes

#reset-options "--z3rlimit 300"

(* BB. Relocate to inttypes ? *)
// let decr (x:size_nat{x > 0}) : size_nat = x - 1
// let incr (x:size_nat{x < max_size_t}) : size_nat = x + 1

let seq a = s:Seq.seq a{Seq.length s <= max_size_t}
let length (#a:Type0) (l:seq a) = Seq.length l

let to_lseq #a (s:seq a) = s
let to_seq #a #len (s:lseq a len) = s

let index #a #len s n = Seq.index s n

abstract
type equal (#a:Type) (#len:size_nat) (s1:lseq a len) (s2:lseq a len) =
 forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i

val eq_intro: #a:Type -> #len:size_nat -> s1:lseq a len -> s2:lseq a len -> Lemma
  (requires (forall (i:size_nat{i < len}).{:pattern (index s1 i); (index s2 i)} index s1 i == index s2 i))
  (ensures  (equal s1 s2))
  [SMTPat (equal s1 s2)]
let eq_intro #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_intro #a s1 s2

val eq_elim: #a:Type -> #len:size_nat -> s1:lseq a len -> s2:lseq a len -> Lemma
  (requires (equal s1 s2))
  (ensures  (s1 == s2))
  [SMTPat (equal s1 s2)]
let eq_elim #a #len s1 s2 =
  assert (forall (i:nat{i < len}).{:pattern (Seq.index s1 i); (Seq.index s2 i)}
    index s1 i == index s2 i);
  Seq.lemma_eq_elim #a s1 s2

let upd #a #len s n x = Seq.upd #a s n x

let create #a len init = Seq.create #a len init

let createL #a l = Seq.createL #a l

let sub #a #len s start n = Seq.slice #a s start (start + n)

let update_sub #a #len s start n x =
  let o =
    Seq.append
      (Seq.append (Seq.slice s 0 start) x)
      (Seq.slice s (start + n) len) in
  Seq.lemma_eq_intro (Seq.slice o start (start + n)) x;
  o

let rec repeat_range #a min max f x =
  if min = max then x
  else repeat_range #a (min + 1) max f (f min x)

let rec repeat_range_ghost #a min max f x =
  if min = max then x
  else repeat_range_ghost #a (min + 1) max f (f min x)

let rec repeat_range_all_ml #a min max f x =
  if min = max then x
  else repeat_range_all_ml #a (min + 1) max f (f min x)

let repeati #a = repeat_range #a 0
let repeati_ghost #a = repeat_range_ghost #a 0
let repeati_all_ml #a = repeat_range_all_ml #a 0
let repeat #a n f x = repeat_range 0 n (fun i -> f) x

unfold
type repeatable (#a:Type) (#n:size_nat) (pred:(i:size_nat{i <= n} -> a -> Tot Type)) =
  i:size_nat{i < n} -> x:a -> Pure a (requires (pred i x)) (ensures (fun r -> pred (i+1) r))

val repeat_range_inductive: #a:Type
  -> min:size_nat
  -> max:size_nat{min <= max}
  -> pred:(i:size_nat{i <= max} -> a -> Type)
  -> f:repeatable #a #max pred
  -> x0:a{pred min x0}
  -> Tot (res:a{pred max res}) (decreases (max - min))

let rec repeat_range_inductive #a min max pred f x =
  if min = max then x
  else repeat_range_inductive #a (min + 1) max pred f (f min x)

val repeati_inductive:
   #a:Type
 -> n:size_nat
 -> pred:(i:size_nat{i <= n} -> a -> Type)
 -> f:repeatable #a #n pred
 -> x0:a{pred 0 x0}
 -> res:a{pred n res}

let repeati_inductive #a =
  repeat_range_inductive #a 0


val fold_left_range_: #a:Type -> #b:Type -> #len:size_nat
  -> min:size_nat
  -> max:size_nat{min <= max /\ len = max - min}
  -> (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b)
  -> lseq a len
  -> b
  -> Tot b (decreases (max - min))

(* let rec fold_left_range_ #a #b #len min max f l x = *)
(*   admit() *)

(* let fold_left_range #a #b #len min max f l x = *)
(*   fold_left_range_ #a #b #(max - min) min max f (slice #a #len l min max) x *)

(* let fold_lefti #a #b #len = fold_left_range #a #b #len 0 len *)

(* let fold_left #a #b #len f = fold_left_range #a #b #len 0 len (fun i -> f) *)

let for_all #a #len f x = Seq.for_all f x

let map #a #b #len f x =
  admit()

let ghost_map #a #b #len f x = admit()

let map2 #a #b #c #len f x y =
  admit()

let rec for_all2 #a #b #len f x y =
  if Seq.length x = 0 then true
  else
    f (Seq.head x) (Seq.head y) && for_all2 #a #b #(len - 1) f (Seq.tail x) (Seq.tail y)

let as_list #a #len l = Seq.Properties.seq_to_list l

val of_list:#a:Type -> l:list a{List.Tot.length l <= maxint U32} -> Tot (seq a)
let of_list #a l =
  let r = Seq.of_list #a l in
  //Seq.lemma_of_list_length #a r l;
  r


let concat #a #len1 #len2 s1 s2 = Seq.append s1 s2

let map_blocks #a bs nb f inp =
  let len = nb * bs in
  let out = inp in
  let out = repeati #(lseq a len) nb
	    (fun i out ->
	         update_slice #a out (i * bs) ((i+1) * bs)
			      (f i (slice #a inp (i * bs) ((i+1) * bs))))
	    out in
  out

let reduce_blocks #a #b bs nb f inp init =
  let len = nb * bs in
  let acc = init in
  let acc = repeati #b nb
	    (fun i acc ->
	       f i (slice #a inp (i * bs) ((i+1) * bs)) acc)
	    acc in
  acc

(* val prefix_: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len} -> Tot (lseq a n) (decreases (n)) *)
(* let rec prefix_ #a #len l n = *)
(*   match n,l with *)
(*   | 0, _ -> [] *)
(*   | n', h::t -> h::prefix_ #a #(decr len) t (decr n) *)

(* let prefix #a #len = prefix_ #a #len *)

(* val suffix: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len} -> Tot (lseq a (len - n)) (decreases (n)) *)
(* let rec suffix #a #len l n = *)
(*   match n,l with *)
(*   | 0, _ ->   l *)
(*   | _, h::t -> suffix #a #(decr len) t (decr n) *)

(* val last: #a:Type -> #len:size_nat{len > 0} -> x:lseq a len -> a *)
(* let last #a #len x = index #a #len x (decr len) *)

(* val snoc: #a:Type -> #len:size_nat{len < maxint U32} -> i:lseq a len -> x:a -> Tot (o:lseq a (incr len){i == prefix #a #(incr len) o len /\ last o == x}) (decreases (len)) *)
(* let rec snoc #a #len i x = *)
(*   match i with *)
(*   | [] -> [x] *)
(*   | h::t -> h::snoc #a #(decr len) t x *)

(* val update_prefix: #a:Type -> #len:size_nat -> lseq a len -> n:size_nat{n <= len} -> x:lseq a n -> Tot (o:lseq a len{sub o 0 n == x}) (decreases (len)) *)
(* let rec update_prefix #a #len l n l' = *)
(*   match n,l,l' with *)
(*   | 0, _, _ -> l *)
(*   | _, h::t, h'::t' -> h':: update_prefix #a #(decr len) t (decr n) t' *)

(* val fold_left_range_: #a:Type -> #b:Type -> #len:size_nat -> min:size_nat -> *)
(*   max:size_nat{min <= max /\ len = max - min} -> *)
(*   (i:size_nat{i >= min /\ i < max} -> a -> b -> Tot b) -> *)
(*   lseq a len -> b -> Tot b (decreases (max - min)) *)
(* let rec fold_left_range_ #a #b #len min max f l x = *)
(*   match l with *)
(*   | [] -> x *)
(*   | h::t -> fold_left_range_ #a #b #(len - 1) (min + 1) max f t (f min h x) *)

(* let fold_left_range #a #b #len min max f l x = *)
(*   fold_left_range_ #a #b #(max - min) min max f (slice #a #len l min max) x *)

(* let fold_lefti #a #b #len = fold_left_range #a #b #len 0 len *)

(* let fold_left #a #b #len f = fold_left_range #a #b #len 0 len (fun i -> f) *)

(*
let fold_left_slices #a #b #len #slice_len f l b =
  let n = lin / slice_len in
  repeati #a n (fun i -> let sl = sub #a #len
*)

(* val map_: #a:Type -> #b:Type -> #len:size_nat -> (a -> Tot b) -> lseq a len -> Tot (lseq b len) (decreases (len)) *)
(* let rec map_ #a #b #len f x = *)
(*   match x with *)
(*   | [] -> [] *)
(*   | h :: t -> *)
(* 	 let t' : lseq a (decr len) = t in *)
(* 	 f h :: map_ #a #b #(decr len) f t' *)
(* let map = map_ *)

(* let slice (#a:Type) (#len:size_nat) (i:lseq a len) (start:size_nat) *)
(* 	  (fin:size_nat{start <= fin /\ fin <= len}) = *)
(* 	  sub #a #len i start (fin - start) *)

(* let update_slice (#a:Type) (#len:size_nat) (i:lseq a len) (start:size_nat) (fin:size_nat{start <= fin /\ fin <= len}) (upd:lseq a (fin - start)) = *)
(* 		 update_sub #a #len i start (fin-start) upd *)

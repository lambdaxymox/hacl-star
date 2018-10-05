module Interop

module List = FStar.List.Tot.Base
module HS = FStar.Monotonic.HyperStack
module HH = FStar.Monotonic.HyperHeap
module B = LowStar.Buffer
module M = LowStar.Modifies
module S8 = SecretByte

open Opaque_s
open X64.Machine_s
open X64.Bytes_Semantics_s
open X64.Bytes_Semantics

open Views

friend SecretByte

#reset-options "--max_fuel 2 --initial_fuel 2 --max_ifuel 1 --initial_ifuel 1"

(* Additional hypotheses, which should be added to the corresponding libraries at some point *)

(* If two refs have the same address, and are in the heap, they are equal *)
assume val ref_extensionality (#a:Type0) (#rel:Preorder.preorder a) (h:Heap.heap) (r1 r2:Heap.mref a rel) : Lemma 
  (Heap.contains h r1 /\ Heap.contains h r2 /\ Heap.addr_of r1 = Heap.addr_of r2 ==> r1 == r2)

private let add_buffer_domain (b:buf) (addrs:addr_map) (accu:Set.set int) : GTot (s:Set.set int{
  forall x. Set.mem x s <==> (Set.mem x accu \/ (x >= addrs b /\ x < addrs b + buf_length b))}) =
  let rec aux (j:nat{j <= buf_length b}) (acc:Set.set int{forall x. Set.mem x acc <==>
    Set.mem x accu \/ (x >= addrs b /\ x < addrs b + j)}) :
    GTot (s:Set.set int{forall x. Set.mem x s <==>
    Set.mem x accu \/ (x >= addrs b /\ x < addrs b + buf_length b)}) 
    (decreases %[buf_length b - j]) = 
    if j >= buf_length b then acc else begin
      let s = Set.union acc (Set.singleton (addrs b + j)) in
      aux (j+1) s
    end in
  aux 0 accu
  

private let rec addrs_set_aux
  (ptrs:list buf)
  (ps2: list buf)
  (ps:list buf{forall b. List.memP b ptrs <==> List.memP b ps \/ List.memP b ps2})
  (addrs:addr_map)
  (accu:Set.set int{forall (x:int). not (Set.mem x accu) <==>
    (forall (b:buf{List.memP b ps}). x < addrs b \/ x >= addrs b + buf_length b)}) :
  GTot (s:Set.set int{forall (x:int). not (Set.mem x s) <==>
    (forall (b:buf{List.memP b ptrs}). x < addrs b \/ x >= addrs b + buf_length b)}) =
  match ps2 with
  | [] -> accu
  | a::q -> 
    let s = add_buffer_domain a addrs accu in
    let aux (x:int) : Lemma
      (requires True)
      (ensures not (Set.mem x s) <==> 
      (forall (b:buf{List.memP b (a::ps)}). 
	x < addrs b \/ x >= addrs b + buf_length b)) = ()
    in
    Classical.forall_intro aux;
    addrs_set_aux ptrs q (a::ps) addrs s

let addrs_set ptrs addrs = addrs_set_aux ptrs ptrs [] addrs Set.empty

let addrs_set_lemma ptrs1 ptrs2 addrs =
  let s1 = addrs_set_aux ptrs1 ptrs1 [] addrs Set.empty in
  let s2 = addrs_set_aux ptrs2 ptrs2 [] addrs Set.empty in
  assert (Set.equal s1 s2)

let addrs_set_concat ptrs a addrs = 
  let s1 = addrs_set ptrs addrs in
  let s2 = addrs_set [a] addrs in
  assert (Set.equal (addrs_set (a::ptrs) addrs) (Set.union s1 s2));
  ()

let addrs_set_mem ptrs a addrs i = ()

(* Write a buffer in the vale memory *)

let rec write_vale_mem8 (contents:Seq.seq UInt8.t) (length:nat{length = Seq.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 
	0 <= j /\ j < i ==> curr_heap.[addr+j] == UInt8.v (Seq.index contents j)}) : Tot heap (decreases %[sub length i]) =
    if i >= length then curr_heap
    else (
      let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
      write_vale_mem8 contents length addr (i+1) heap
    )      

let rec frame_write_vale_mem8 (contents:Seq.seq UInt8.t) (length:nat{length = FStar.Seq.Base.length contents}) addr (i:nat{i <= length}) 
      (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem8 contents length addr i curr_heap in
      forall j. j < addr \/ j >= addr + length ==> curr_heap.[j] == new_heap.[j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
	let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
	frame_write_vale_mem8 contents length addr (i+1) heap
      end
      
let rec load_store_write_vale_mem8
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem8 contents length addr i curr_heap in
      forall j. 0 <= j /\ j < length ==> UInt8.v (Seq.index contents j) == new_heap.[addr + j]))
      (decreases %[sub length i])=
      if i >= length then ()
      else begin
	let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
	load_store_write_vale_mem8 contents length addr (i+1) heap
      end

let rec domain_write_vale_mem8
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem8 contents length addr i curr_heap in
      forall j. Set.mem j (Map.domain new_heap) /\ not (Set.mem j (Map.domain curr_heap)) ==> 
        addr <= j /\ j < addr + length))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     domain_write_vale_mem8 contents length addr (i+1) heap
    end

let rec domain2_write_vale_mem8 
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires forall j. addr <= j /\ j < addr + i ==> Set.mem j (Map.domain curr_heap))
      (ensures (let new_heap = write_vale_mem8 contents length addr i curr_heap in
	forall j. addr <= j /\ j < addr + length ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     domain2_write_vale_mem8 contents length addr (i+1) heap
    end

let rec monotone_domain_write_vale_mem8
  (contents:Seq.seq UInt8.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    curr_heap.[addr + j] == UInt8.v (Seq.index contents j)}) : Lemma
      (requires True)
      (ensures (let new_heap = write_vale_mem8 contents length addr i curr_heap in
      forall j. Set.mem j (Map.domain curr_heap) ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
     let heap = curr_heap.[addr + i] <- UInt8.v (FStar.Seq.index contents i) in
     monotone_domain_write_vale_mem8 contents length addr (i+1) heap
    end

#set-options "--z3rlimit 10"

let rec write_vale_mem32 
  (contents:Seq.seq UInt32.t) 
  (length:nat{length = Seq.length contents}) 
  addr
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    (forall k. 0 <= k /\ k < 4 ==> 
      curr_heap.[addr+ 4 `op_Multiply` j + k] == 
      UInt8.v (Seq.index (put32_def (Seq.index contents j)) k))}) :
  GTot heap (decreases %[sub length i]) =
    if i >= length then curr_heap
    else (
      let put = put32_def (Seq.index contents i) in
      let heap = curr_heap.[addr + 4 `op_Multiply` i + 0] <- UInt8.v (Seq.index put 0) in
      let heap = heap.[addr + 4 `op_Multiply` i + 1] <- UInt8.v (Seq.index put 1) in
      let heap = heap.[addr + 4 `op_Multiply` i + 2] <- UInt8.v (Seq.index put 2) in
      let heap = heap.[addr + 4 `op_Multiply` i + 3] <- UInt8.v (Seq.index put 3) in      
      write_vale_mem32 contents length addr (i+1) heap
    )      

let rec frame_write_vale_mem32
  (contents:Seq.seq UInt32.t)
  (length:nat{length = Seq.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==>
    (forall k. 0 <= k /\ k < 4 ==> 
      curr_heap.[addr + 4 `op_Multiply` j + k] == 
      UInt8.v (Seq.index (put32_def (Seq.index contents j)) k))}) : 
  Lemma
    (requires True)
    (ensures (
      let new_heap = write_vale_mem32 contents length addr i curr_heap in
      forall j. j < addr \/ j >= addr + 4 `op_Multiply` length ==> curr_heap.[j] == new_heap.[j]))
      (decreases %[sub length i]) =
   if i >= length then ()
   else begin
      let put = put32_def (Seq.index contents i) in
      let heap = curr_heap.[addr + 4 `op_Multiply` i + 0] <- UInt8.v (Seq.index put 0) in
      let heap = heap.[addr + 4 `op_Multiply` i + 1] <- UInt8.v (Seq.index put 1) in
      let heap = heap.[addr + 4 `op_Multiply` i + 2] <- UInt8.v (Seq.index put 2) in
      let heap = heap.[addr + 4 `op_Multiply` i + 3] <- UInt8.v (Seq.index put 3) in  
      frame_write_vale_mem32 contents length addr (i+1) heap
   end
      
let rec load_store_write_vale_mem32 
  (contents:Seq.seq UInt32.t) 
  (length:nat{length = FStar.Seq.Base.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    (forall k. 0 <= k /\ k < 4 ==> 
      curr_heap.[addr + 4 `op_Multiply` j + k] == 
      UInt8.v (Seq.index (put32_def (Seq.index contents j)) k))}) : 
  Lemma
    (requires True)
    (ensures (
      let new_heap = write_vale_mem32 contents length addr i curr_heap in
      forall j. 0 <= j /\ j < length ==>
        (forall k. 0 <= k /\ k < 4 ==> 
          new_heap.[addr + 4 `op_Multiply` j + k] == 
          UInt8.v (Seq.index (put32_def (Seq.index contents j)) k))))
      (decreases %[sub length i])=
  if i >= length then ()
  else begin
    let put = put32_def (Seq.index contents i) in
    let heap = curr_heap.[addr + 4 `op_Multiply` i + 0] <- UInt8.v (Seq.index put 0) in
    let heap = heap.[addr + 4 `op_Multiply` i + 1] <- UInt8.v (Seq.index put 1) in
    let heap = heap.[addr + 4 `op_Multiply` i + 2] <- UInt8.v (Seq.index put 2) in
    let heap = heap.[addr + 4 `op_Multiply` i + 3] <- UInt8.v (Seq.index put 3) in  
    load_store_write_vale_mem32 contents length addr (i+1) heap
  end

let rec domain_write_vale_mem32 
  (contents:Seq.seq UInt32.t) 
  (length:nat{length = Seq.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    (forall k. 0 <= k /\ k < 4 ==> 
      curr_heap.[addr + 4 `op_Multiply` j + k] == 
      UInt8.v (Seq.index (put32_def (Seq.index contents j)) k))}) : 
  Lemma
    (requires True)
    (ensures (
      let new_heap = write_vale_mem32 contents length addr i curr_heap in
      forall j. Set.mem j (Map.domain new_heap) /\ not (Set.mem j (Map.domain curr_heap)) ==> 
      addr <= j /\ j < addr + 4 `op_Multiply` length))
      (decreases %[sub length i])=
   if i >= length then ()
   else begin
    let put = put32_def (Seq.index contents i) in
    let heap = curr_heap.[addr + 4 `op_Multiply` i + 0] <- UInt8.v (Seq.index put 0) in
    let heap = heap.[addr + 4 `op_Multiply` i + 1] <- UInt8.v (Seq.index put 1) in
    let heap = heap.[addr + 4 `op_Multiply` i + 2] <- UInt8.v (Seq.index put 2) in
    let heap = heap.[addr + 4 `op_Multiply` i + 3] <- UInt8.v (Seq.index put 3) in  
    domain_write_vale_mem32 contents length addr (i+1) heap
  end

let rec domain2_write_vale_mem32
  (contents:Seq.seq UInt32.t) 
  (length:nat{length = Seq.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    (forall k. 0 <= k /\ k < 4 ==> 
      curr_heap.[addr + 4 `op_Multiply` j + k] == 
      UInt8.v (Seq.index (put32_def (Seq.index contents j)) k))}) : 
  Lemma
    (requires forall j. addr <= j /\ j < addr + 4 `op_Multiply` i ==> Set.mem j (Map.domain curr_heap))
    (ensures (  
      let new_heap = write_vale_mem32 contents length addr i curr_heap in
      forall j. addr <= j /\ j < addr + 4 `op_Multiply` length ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
  if i >= length then ()
  else begin
    let put = put32_def (Seq.index contents i) in
    let heap = curr_heap.[addr + 4 `op_Multiply` i + 0] <- UInt8.v (Seq.index put 0) in
    let heap = heap.[addr + 4 `op_Multiply` i + 1] <- UInt8.v (Seq.index put 1) in
    let heap = heap.[addr + 4 `op_Multiply` i + 2] <- UInt8.v (Seq.index put 2) in
    let heap = heap.[addr + 4 `op_Multiply` i + 3] <- UInt8.v (Seq.index put 3) in  
    domain2_write_vale_mem32 contents length addr (i+1) heap
  end

let rec monotone_domain_write_vale_mem32
  (contents:Seq.seq UInt32.t) 
  (length:nat{length = Seq.length contents}) 
  addr 
  (i:nat{i <= length}) 
  (curr_heap:heap{forall j. {:pattern (Seq.index contents j)} 0 <= j /\ j < i ==> 
    (forall k. 0 <= k /\ k < 4 ==> 
      curr_heap.[addr + 4 `op_Multiply` j + k] == 
      UInt8.v (Seq.index (put32_def (Seq.index contents j)) k))}) :
  Lemma
      (requires True)
      (ensures (
        let new_heap = write_vale_mem32 contents length addr i curr_heap in
        forall j. Set.mem j (Map.domain curr_heap) ==> Set.mem j (Map.domain new_heap)))
      (decreases %[sub length i])=
  if i >= length then ()
  else begin
    let put = put32_def (Seq.index contents i) in
    let heap = curr_heap.[addr + 4 `op_Multiply` i + 0] <- UInt8.v (Seq.index put 0) in
    let heap = heap.[addr + 4 `op_Multiply` i + 1] <- UInt8.v (Seq.index put 1) in
    let heap = heap.[addr + 4 `op_Multiply` i + 2] <- UInt8.v (Seq.index put 2) in
    let heap = heap.[addr + 4 `op_Multiply` i + 3] <- UInt8.v (Seq.index put 3) in 
    monotone_domain_write_vale_mem32 contents length addr (i+1) heap
  end

let write_buffer_vale (b:buf) (heap:heap) (mem:HS.mem) (addrs:addr_map) = match b with
  | B8 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    write_vale_mem8 contents length addr 0 heap
  | B32 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    write_vale_mem32 contents length addr 0 heap

let frame_write_vale_mem
  (b:buf)
  (heap:heap)
  (mem:HS.mem)
  (addrs:addr_map) :
  Lemma (
    let new_heap = write_buffer_vale b heap mem addrs in
    forall j. j < addrs b \/ j >= addrs b + buf_length b ==> heap.[j] == new_heap.[j]) =
  match b with
  | B8 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    frame_write_vale_mem8 contents length addr 0 heap
  | B32 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    frame_write_vale_mem32 contents length addr 0 heap

let domain_write_vale_mem
  (b:buf)
  (heap:heap)
  (mem:HS.mem)
  (addrs:addr_map) :
  Lemma (
    let new_heap = write_buffer_vale b heap mem addrs in
    forall j. Set.mem j (Map.domain new_heap) /\ not (Set.mem j (Map.domain heap)) ==> 
    addrs b <= j /\ j < addrs b + buf_length b) =
  match b with
  | B8 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    domain_write_vale_mem8 contents length addr 0 heap
  | B32 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    domain_write_vale_mem32 contents length addr 0 heap

let domain2_write_vale_mem
  (b:buf)
  (heap:heap)
  (mem:HS.mem)
  (addrs:addr_map) :
  Lemma (
    let new_heap = write_buffer_vale b heap mem addrs in
    forall j. addrs b <= j /\ j < addrs b + buf_length b ==> Set.mem j (Map.domain new_heap)) =
  match b with
  | B8 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    domain2_write_vale_mem8 contents length addr 0 heap
  | B32 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    domain2_write_vale_mem32 contents length addr 0 heap


let monotone_domain_write_vale_mem
  (b:buf)
  (heap:heap)
  (mem:HS.mem)
  (addrs:addr_map) :
  Lemma (
    let new_heap = write_buffer_vale b heap mem addrs in
    forall j. Set.mem j (Map.domain heap) ==> Set.mem j (Map.domain new_heap)) =
  match b with
  | B8 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    monotone_domain_write_vale_mem8 contents length addr 0 heap
  | B32 a ->
    let length = B.length a in
    let contents = B.as_seq mem a in
    let addr = addrs b in
    monotone_domain_write_vale_mem32 contents length addr 0 heap

let domain_write_buffer 
  (a:buf) 
  (heap:heap) 
  (mem:HS.mem) 
  (addrs:addr_map) :
  Lemma
    (let new_heap = write_buffer_vale a heap mem addrs in
     Set.equal 
       (Set.union (Map.domain heap) (addrs_set [a] addrs))
       (Map.domain new_heap)) =
   domain_write_vale_mem a heap mem addrs;
   domain2_write_vale_mem a heap mem addrs;
   monotone_domain_write_vale_mem a heap mem addrs

let correct_down_p_cancel mem (addrs:addr_map) heap (p:buf) : Lemma
  (forall p'. p == p' ==>       
    (let new_heap = write_buffer_vale p heap mem addrs in
    correct_down_p mem addrs new_heap p')) = 
  let aux (p':buf) : Lemma 
    (p == p' ==>
      (let new_heap = write_buffer_vale p heap mem addrs in    
      correct_down_p mem addrs new_heap p')) =
      let new_heap = write_buffer_vale p heap mem addrs in
        match p with
        | B8 p ->
          let length = B.length p in
          let contents = B.as_seq mem p in
          let addr = addrs (B8 p) in
	  load_store_write_vale_mem8 contents length addr 0 heap
        | B32 p ->
          let length = B.length p in
          let contents = B.as_seq mem p in
          let addr = addrs (B32 p) in
	  load_store_write_vale_mem32 contents length addr 0 heap
  in
  Classical.forall_intro aux
      
let correct_down_p_frame mem (addrs:addr_map) (heap:heap) (p:buf) : Lemma
  (forall p'. disjoint p p' /\ correct_down_p mem addrs heap p' ==>       
    (let new_heap = write_buffer_vale p heap mem addrs in
    correct_down_p mem addrs new_heap p')) = 
  let aux (p':buf) : Lemma 
    (disjoint p p' /\ correct_down_p mem addrs heap p' ==> 
      (let new_heap = write_buffer_vale p heap mem addrs in
      correct_down_p mem addrs new_heap p')) =
    let new_heap = write_buffer_vale p heap mem addrs in
    match p with
    | B8 p ->
      let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs (B8 p) in
      frame_write_vale_mem8 contents length addr 0 heap
    | B32 p ->
      let length = B.length p in
      let contents = B.as_seq mem p in
      let addr = addrs (B32 p) in
      frame_write_vale_mem32 contents length addr 0 heap
  in
  Classical.forall_intro aux

let rec down_mem_aux (ptrs:list buf{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list buf)
  (accu:list buf{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) : 
  GTot (heap:heap{correct_down mem addrs ptrs heap}) =
  match ps with
    | [] -> addrs_set_lemma accu ptrs addrs; h
    | a::q ->
      let new_heap = write_buffer_vale a h mem addrs in
      correct_down_p_cancel mem addrs h a;
      correct_down_p_frame mem addrs h a;
      assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
      domain_write_buffer a h mem addrs;
      addrs_set_concat accu a addrs;
      down_mem_aux ptrs addrs mem q (a::accu) new_heap

let down_mem mem addrs ptrs =
  (* Dummy heap *)
  let heap = FStar.Map.const 0 in
  let heap = Map.restrict Set.empty heap in
  down_mem_aux ptrs addrs mem ptrs [] heap

private
let rec frame_down_mem_aux (ptrs:list buf{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (ps:list buf)
  (accu:list buf{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})
  (h:heap{correct_down mem addrs accu h}) : Lemma
  (let heap = down_mem_aux ptrs addrs mem ps accu h in
   forall i. (forall (b:buf{List.memP b ptrs}). 
      let base = addrs b in
      i < base \/ i >= base + buf_length b) ==>
      h.[i] == heap.[i]) =
  match ps with
  | [] -> ()
  | a::q ->
    let new_heap = write_buffer_vale a h mem addrs in
    correct_down_p_cancel mem addrs h a;
    correct_down_p_frame mem addrs h a;
    assert (forall p. List.memP p accu ==> disjoint_or_eq p a);
    domain_write_buffer a h mem addrs;
    addrs_set_concat accu a addrs;    
    frame_down_mem_aux ptrs addrs mem q (a::accu) new_heap;
    frame_write_vale_mem a h mem addrs;
    ()

let same_unspecified_down mem1 mem2 addrs ptrs =
  let heap = Map.const 0 in
  let heap = Map.restrict Set.empty heap in
  let heapf1 = down_mem_aux ptrs addrs mem1 ptrs [] heap in
  let heapf2 = down_mem_aux ptrs addrs mem2 ptrs [] heap in
  frame_down_mem_aux ptrs addrs mem1 ptrs [] heap;
  frame_down_mem_aux ptrs addrs mem2 ptrs [] heap;
  ()

let buf_as_seq (mem:HS.mem) (b:buf) : GTot (if B8? b then Seq.seq UInt8.t else Seq.seq UInt32.t) = match b with
  | B8 b -> B.as_seq mem b
  | B32 b -> B.as_seq mem b

#set-options "--z3rlimit 20"

let get_seq_heap_as_seq 
  (heap1 heap2:heap) 
  (addrs:addr_map) 
  (mem:HS.mem) 
  (b:buf) : Lemma
  (requires correct_down_p mem addrs heap1 b /\
    (forall x. x >= addrs b /\ x < addrs b + buf_length b ==> heap1.[x] == heap2.[x]))
  (ensures buf_as_seq mem b == get_seq_heap heap2 addrs b) =
  match b with
  | B8 b ->
    assert (Seq.equal (B.as_seq mem b) (get_seq_heap heap2 addrs (B8 b)))
  | B32 a ->
    reveal_opaque get32_def;
    let seq_heap = get_seq_heap heap2 addrs b in
    let aux (i:nat{i < B.length a}) =
      // assume (Seq.index seq_heap i == UInt32.uint_to_t (
      // heap2.[addrs b + 4 `op_Multiply` i + 0] +
      // heap2.[addrs b + 4 `op_Multiply` i + 1] `op_Multiply` 0x100 +
      // heap2.[addrs b + 4 `op_Multiply` i + 2] `op_Multiply` 0x10000 +
      // heap2.[addrs b + 4 `op_Multiply` i + 3] `op_Multiply` 0x1000000));
      ()

      // let s2 = Seq.init 4 (fun (j:nat{j < 4}) -> heap2.[addrs (B32 b) + 4 `op_Multiply` i + j]) in
      // assert (get32 s2 == Seq.index (get_seq_heap heap2 addrs (B32 b)) i)
    in   
    // assert (forall (i:nat{i < B.length b}). 
    //   Seq.index (get_seq_heap heap2 addrs (B32 b)) i == 
    //   get32 (Seq.init 4 (fun (j:nat{j < 4}) -> heap2.[addrs (B32 b) + 4 `op_Multiply` i + j])));
    admit();
    assert (Seq.equal (B.as_seq mem a) (get_seq_heap heap2 addrs b))

let rec up_mem_aux (heap:heap)
               (addrs:addr_map)
               (ptrs:list buf{list_disjoint_or_eq ptrs})
               (ps:list buf)
               (accu:list buf{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) 
               (m:HS.mem{list_live m ptrs /\ 
                 Set.equal (addrs_set ptrs addrs) (Map.domain heap) /\ 
                 (forall p. List.memP p accu ==> correct_down_p m addrs heap p)})
  : GTot (m':HS.mem{correct_down m' addrs ptrs heap /\ list_live m' ptrs}) =
    match ps with
    | [] -> m
    | (B8 a)::q ->
      let s = get_seq_heap heap addrs (B8 a) in
      B.g_upd_seq_as_seq a s m;
      let m' = B.g_upd_seq a s m in
      admit();
      up_mem_aux heap addrs ptrs q ((B8 a)::accu) m'
    | (B32 a)::q -> admit()

let up_mem heap addrs ptrs mem = up_mem_aux heap addrs ptrs ptrs [] mem

let rec down_up_identity_aux
    (heap:heap)
    (addrs:addr_map)
    (ptrs:list buf{list_disjoint_or_eq ptrs})
    (ps:list buf)
    (accu:list buf{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu})    
    (m:HS.mem{list_live m ptrs /\ correct_down m addrs ptrs heap})
  : Lemma (m == up_mem_aux heap addrs ptrs ps accu m) =
  match ps with
  | [] -> ()
  | a::q ->
      let s = get_seq_heap heap addrs a in
      let m' = B.g_upd_seq a s m in
      B.lemma_g_upd_with_same_seq a m;
      assert (Seq.equal s (B.as_seq m a));
      (* The previous assertion and lemma ensure that m == m' *)
      B.g_upd_seq_as_seq a s m;
      down_up_identity_aux heap addrs ptrs q (a::accu) m'

let down_up_identity mem addrs ptrs =
  let heap = down_mem mem addrs ptrs in
  down_up_identity_aux heap addrs ptrs ptrs [] mem

let correct_down_p_same_sel (b:b8) (mem:HS.mem) (addrs:addr_map) (heap1 heap2:heap) (x:int) : Lemma
  (requires (x >= addrs b /\ x < addrs b + B.length b 
    /\ correct_down_p mem addrs heap1 b /\ correct_down_p mem addrs heap2 b))
  (ensures Map.sel heap1 x == Map.sel heap2 x) = 
    let i = x - addrs b in
    assert (heap1.[x] == heap1.[addrs b + i]);
    assert (heap2.[x] == heap2.[addrs b + i])

let rec up_down_identity_aux
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem)
  (init_heap:heap{correct_down mem addrs ptrs init_heap})
  : Lemma 
      (let heap = down_mem mem addrs ptrs in 
      forall x. Map.contains heap x ==> Map.sel heap x == Map.sel init_heap x) =
    let heap = down_mem mem addrs ptrs in
    let aux (x:int) : Lemma 
      (requires Map.contains heap x)
      (ensures Map.sel heap x == Map.sel init_heap x) =
      Classical.forall_intro 
        (Classical.move_requires (fun b -> correct_down_p_same_sel b mem addrs heap init_heap x))
    in Classical.forall_intro (Classical.move_requires aux)

let up_down_identity mem addrs ptrs heap = 
  let initial_heap = down_mem mem addrs ptrs in
  let new_heap = down_mem (up_mem heap addrs ptrs mem) addrs ptrs in
  same_unspecified_down mem (up_mem heap addrs ptrs mem) addrs ptrs;
  up_down_identity_aux ptrs addrs (up_mem heap addrs ptrs mem) heap;
  assert (Map.equal heap new_heap)

#set-options "--max_fuel 1 --max_ifuel 1"

let g_upd_tot_correct_down_invariant
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (heap1:heap)
  (heap2:heap)
  (b:b8{List.memP b ptrs})
  (mem:HS.mem{list_live mem ptrs})
  : Lemma
  (requires forall p. (p =!= b /\ List.memP p ptrs) ==> correct_down_p mem addrs heap1 p)
  (ensures (
    let m' = B.g_upd_seq b (get_seq_heap heap2 addrs b) mem in
    forall p. (p =!= b /\ List.memP p ptrs) ==> correct_down_p m' addrs heap1 p)
  ) = 
    B.g_upd_seq_as_seq b (get_seq_heap heap2 addrs b) mem

let g_upd_tot_correct_down
  (mem:HS.mem)
  (addrs:addr_map)
  (heap:heap)
  (b:b8{B.live mem b}) :
  Lemma (correct_down_p (B.g_upd_seq b (get_seq_heap heap addrs b) mem) addrs heap b) =
  B.g_upd_seq_as_seq b (get_seq_heap heap addrs b) mem

#reset-options "--z3rlimit 50 --max_fuel 1 --max_ifuel 1 --initial_fuel 1 --initial_ifuel 1"
let rec update_buffer_up_mem_aux
  (ptrs:list b8{list_disjoint_or_eq ptrs})
  (addrs:addr_map)
  (mem:HS.mem{list_live mem ptrs})
  (b:b8{List.memP b ptrs})
  (heap1:heap{Set.equal (Map.domain heap1) (addrs_set ptrs addrs)})
  (heap2:heap{Set.equal (Map.domain heap1) (Map.domain heap2)})
  (ps:list b8)
  (accu:list b8{forall p. List.memP p ptrs <==> List.memP p ps \/ List.memP p accu}) : Lemma
  (requires (forall x. x < addrs b \/ x >= addrs b + B.length b ==> heap1.[x] == heap2.[x]) /\
    (List.memP b accu ==> B.as_seq mem b == get_seq_heap heap2 addrs b) /\  
    (forall p. List.memP p accu ==> correct_down_p mem addrs heap2 p) /\
    (forall p. (p =!= b /\ List.memP p ptrs) ==> correct_down_p mem addrs heap1 p)    )
  (ensures 
  (List.memP b accu ==> up_mem_aux heap2 addrs ptrs ps accu mem == mem) /\
  (~(List.memP b accu) ==> up_mem_aux heap2 addrs ptrs ps accu mem ==
    B.g_upd_seq b (get_seq_heap heap2 addrs b) mem))
  (decreases ps)
  
  = match ps with
   | [] -> ()
   | a::q ->
     let s = get_seq_heap heap2 addrs a in       
     B.g_upd_seq_as_seq a s mem;         
     let m' = B.g_upd_seq a s mem in
     if StrongExcludedMiddle.strong_excluded_middle (a == b) then (
       if StrongExcludedMiddle.strong_excluded_middle (List.memP b accu) then (
         B.lemma_g_upd_with_same_seq a mem;       
         update_buffer_up_mem_aux ptrs addrs m' b heap1 heap2 q (a::accu)
       ) else (
         g_upd_tot_correct_down_invariant ptrs addrs heap1 heap2 b mem;
         g_upd_tot_correct_down mem addrs heap2 b;
         update_buffer_up_mem_aux ptrs addrs m' b heap1 heap2 q (a::accu)
       )
     ) else (
       assert (B.disjoint a b);
       get_seq_heap_as_seq heap1 heap2 addrs mem a;
       B.lemma_g_upd_with_same_seq a mem;       
       update_buffer_up_mem_aux ptrs addrs m' b heap1 heap2 q (a::accu)
     )

let update_buffer_up_mem ptrs addrs mem b heap1 heap2 =
  update_buffer_up_mem_aux ptrs addrs mem b heap1 heap2 ptrs []

module Lib.IntTypes

(* Declared in .fsti : intsize, bits, maxint *)
#set-options "--z3rlimit 20 --max_fuel 0 --max_ifuel 1"

let pow2_values n =
    assert_norm (pow2 0 = 1);
    assert_norm (pow2 1 = 2);
    assert_norm (pow2 2 = 4);
    assert_norm (pow2 3 = 8);
    assert_norm (pow2 4 = 16);
    assert_norm (pow2 8 = 0x100);
    assert_norm (pow2 16 = 0x10000);
    assert_norm (pow2 32 = 0x100000000);
    assert_norm (pow2 64 = 0x10000000000000000);
    assert_norm (pow2 128 = 0x100000000000000000000000000000000)

let sec_int_t (t:inttype) = pub_int_t t

let sec_int_v #t (u:sec_int_t t) = pub_int_v #t u

let uintv_extensionality #t #l a b =
  match t with
  | U1   -> ()
  | U8   -> UInt8.v_inj a b
  | U16  -> UInt16.v_inj a b
  | U32  -> UInt32.v_inj a b
  | U64  -> UInt64.v_inj a b
  | U128 -> UInt128.v_inj a b

(* Declared in .fsti: uint8, uint16, uint32, uint64, uint128 *)

let secret #t x = x

let uint #t #l x =
  match t with
  | U1 -> UInt8.uint_to_t x
  | U8 -> UInt8.uint_to_t x
  | U16 -> UInt16.uint_to_t x
  | U32 -> UInt32.uint_to_t x
  | U64 -> UInt64.uint_to_t x
  | U128 -> UInt128.uint_to_t x

let u8 x : uint8  = UInt8.uint_to_t x

let u16 x : uint16 = UInt16.uint_to_t x

let u16_us x = x

let u32 x : uint32 = UInt32.uint_to_t x

let u32_ul x = x

let u64 x : uint64 = UInt64.uint_to_t x

let u64_uL x = x

let u128 x : uint128 = UInt128.uint_to_t x

inline_for_extraction
let size_ x : uint_t U32 PUB = UInt32.uint_to_t x

inline_for_extraction
let byte_ x : uint_t U8 PUB = UInt8.uint_to_t x

inline_for_extraction
let size x = size_ x

inline_for_extraction
let byte x = byte_ x

let size_to_uint32 x = x <: UInt32.t

let byte_to_uint8 x = x <: UInt8.t

let nat_to_uint #t #l x : uint_t t l =
  match t with
  | U1 -> u8 x
  | U8 -> u8 x
  | U16 -> u16 x
  | U32 -> u32 x
  | U64 -> u64 x
  | U128 -> u128 x

#reset-options "--z3rlimit 1000 --max_fuel 0"
#set-options "--lax" // TODO: remove this
let cast #t #l t' l' u  =
  match t, t' with
  | U1, U1 -> u
  | U1, U8 -> u
  | U1, U16 -> FStar.Int.Cast.uint8_to_uint16 u
  | U1, U32 -> FStar.Int.Cast.uint8_to_uint32 u
  | U1, U64 -> FStar.Int.Cast.uint8_to_uint64 u
  | U1, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint8_to_uint64 u)
  | U8, U1 -> FStar.UInt8.logand u (0x1uy)
  | U8, U8 -> u
  | U8, U16 -> FStar.Int.Cast.uint8_to_uint16 u
  | U8, U32 -> FStar.Int.Cast.uint8_to_uint32 u
  | U8, U64 -> FStar.Int.Cast.uint8_to_uint64 u
  | U8, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint8_to_uint64 u)
  | U16, U1 -> FStar.UInt8.logand (FStar.Int.Cast.uint16_to_uint8 u) (0x1uy)
  | U16, U8 -> FStar.Int.Cast.uint16_to_uint8 u
  | U16, U16 -> u
  | U16, U32 -> FStar.Int.Cast.uint16_to_uint32 u
  | U16, U64 -> FStar.Int.Cast.uint16_to_uint64 u
  | U16, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint16_to_uint64 u)
  | U32, U1 -> FStar.UInt8.logand (FStar.Int.Cast.uint32_to_uint8 u) (0x1uy)
  | U32, U8 -> FStar.Int.Cast.uint32_to_uint8 u
  | U32, U16 -> FStar.Int.Cast.uint32_to_uint16 u
  | U32, U32 -> u
  | U32, U64 -> FStar.Int.Cast.uint32_to_uint64 u
  | U32, U128 -> FStar.UInt128.uint64_to_uint128 (FStar.Int.Cast.uint32_to_uint64 u)
  | U64, U1 -> FStar.UInt8.logand (FStar.Int.Cast.uint64_to_uint8 u) (0x1uy)
  | U64, U8 -> FStar.Int.Cast.uint64_to_uint8 u
  | U64, U16 -> FStar.Int.Cast.uint64_to_uint16 u
  | U64, U32 -> FStar.Int.Cast.uint64_to_uint32 u
  | U64, U64 -> u
  | U64, U128 -> FStar.UInt128.uint64_to_uint128 u
  | U128, U1 -> FStar.UInt8.logand (FStar.Int.Cast.uint64_to_uint8 (FStar.UInt128.uint128_to_uint64 u)) (0x1uy)
  | U128, U8 -> FStar.Int.Cast.uint64_to_uint8 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U16 -> FStar.Int.Cast.uint64_to_uint16 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U32 -> FStar.Int.Cast.uint64_to_uint32 (FStar.UInt128.uint128_to_uint64 u)
  | U128, U64 -> FStar.UInt128.uint128_to_uint64 u
  | U128, U128 -> u

#reset-options "--z3rlimit 100"

let add_mod #t #l a b =
  match t with
  | U1  -> UInt8.rem (UInt8.add_mod a b) 2uy
  | U8  -> (UInt8.add_mod a b)
  | U16 -> (UInt16.add_mod a b)
  | U32 -> (UInt32.add_mod a b)
  | U64 -> (UInt64.add_mod a b)
  | U128 -> (UInt128.add_mod a b)

let add #t #l a b =
  match t with
  | U1 -> (UInt8.add a b)
  | U8 -> (UInt8.add a b)
  | U16 -> (UInt16.add a b)
  | U32 -> (UInt32.add a b)
  | U64 -> (UInt64.add a b)
  | U128 -> (UInt128.add a b)

let incr #t #l a =
  match t with
  | U1 -> (UInt8.add a 0x1uy)
  | U8 -> (UInt8.add a 0x1uy)
  | U16 -> (UInt16.add a 0x1us)
  | U32 -> (UInt32.add a 0x1ul)
  | U64 -> (UInt64.add a 0x1uL)
  | U128 -> (UInt128.add a (UInt128.uint_to_t 1))

let mul_mod #t #l a b =
  match t with
  | U1 -> (UInt8.mul_mod a b)
  | U8 -> (UInt8.mul_mod a b)
  | U16 -> (UInt16.mul_mod a b)
  | U32 -> (UInt32.mul_mod a b)
  | U64 -> (UInt64.mul_mod a b)

let mul #t #l a b =
  match t with
  | U1 -> (UInt8.mul a b)
  | U8 -> (UInt8.mul a b)
  | U16 -> (UInt16.mul a b)
  | U32 -> (UInt32.mul a b)
  | U64 -> (UInt64.mul a b)

let mul64_wide a b = UInt128.mul_wide a b

let sub_mod #t #l a b =
  match t with
  | U1 -> UInt8.rem (UInt8.sub_mod a b) 0x2uy
  | U8 -> (UInt8.sub_mod a b)
  | U16 -> (UInt16.sub_mod a b)
  | U32 -> (UInt32.sub_mod a b)
  | U64 -> (UInt64.sub_mod a b)
  | U128 -> (UInt128.sub_mod a b)

let sub #t #l a b =
  match t with
  | U1 -> (UInt8.sub a b)
  | U8 -> (UInt8.sub a b)
  | U16 -> (UInt16.sub a b)
  | U32 -> (UInt32.sub a b)
  | U64 -> (UInt64.sub a b)
  | U128 -> (UInt128.sub a b)

let decr #t #l a =
  match t with
  | U1 -> (UInt8.sub a 0x1uy)
  | U8 -> (UInt8.sub a 0x1uy)
  | U16 -> (UInt16.sub a 0x1us)
  | U32 -> (UInt32.sub a 0x1ul)
  | U64 -> (UInt64.sub a 0x1uL)
  | U128 -> (UInt128.sub a (UInt128.uint_to_t 1))

let logxor #t #l a b =
  match t with
  | U1 -> (UInt8.logxor a b)
  | U8 -> (UInt8.logxor a b)
  | U16 -> (UInt16.logxor a b)
  | U32 -> (UInt32.logxor a b)
  | U64 -> (UInt64.logxor a b)
  | U128 -> (UInt128.logxor a b)

let logand #t #l a b =
  match t with
  | U1 -> (UInt8.logand a b)
  | U8 -> (UInt8.logand a b)
  | U16 -> (UInt16.logand a b)
  | U32 -> (UInt32.logand a b)
  | U64 -> (UInt64.logand a b)
  | U128 -> (UInt128.logand a b)

let logor #t #l a b =
  match t with
  | U1 -> (UInt8.logor a b)
  | U8 -> (UInt8.logor a b)
  | U16 -> (UInt16.logor a b)
  | U32 -> (UInt32.logor a b)
  | U64 -> (UInt64.logor a b)
  | U128 -> (UInt128.logor a b)

let lognot #t #l a =
  match t with
  | U1 -> UInt8.rem (UInt8.lognot a) 0x2uy
  | U8 -> (UInt8.lognot a)
  | U16 -> (UInt16.lognot a)
  | U32 -> (UInt32.lognot a)
  | U64 -> (UInt64.lognot a)
  | U128 -> (UInt128.lognot a)

let shift_right #t #l a b =
  match t with
  | U1 -> (UInt8.shift_right a b)
  | U8 -> (UInt8.shift_right a b)
  | U16 -> (UInt16.shift_right a b)
  | U32 -> (UInt32.shift_right a b)
  | U64 -> (UInt64.shift_right a b)
  | U128 -> (UInt128.shift_right a b)

let shift_left #t #l a b =
  match t with
  | U1 -> (UInt8.shift_left a b)
  | U8 -> (UInt8.shift_left a b)
  | U16 -> (UInt16.shift_left a b)
  | U32 -> (UInt32.shift_left a b)
  | U64 -> (UInt64.shift_left a b)
  | U128 -> (UInt128.shift_left a b)

let rotate_right #t #l a b =
  (logor (shift_right a b)  (shift_left a (sub #U32 (size (bits t)) b)))

let rotate_left #t #l a b =
  (logor (shift_left a b)  (shift_right a (sub #U32 (size (bits t)) b)))

let zeroes t l = nat_to_uint #t #l 0

let ones t l =
  match t with
  | U1 -> 0x1uy
  | U8 -> 0xffuy
  | U16 -> 0xffffus
  | U32 -> 0xfffffffful
  | U64 -> 0xffffffffffffffffuL
  | U128 ->
    let x = FStar.UInt128.uint64_to_uint128 0xffffffffffffffffuL in
	 let y = (FStar.UInt128.shift_left x 64ul) `FStar.UInt128.add` x in
    assert_norm(FStar.UInt128.v y == pow2 128 - 1);
    y

let eq_mask #t #l a b =
  match t with
  | U1 -> lognot (logxor a b)
  | U8 -> UInt8.eq_mask a b
  | U16 -> UInt16.eq_mask a b
  | U32 -> UInt32.eq_mask a b
  | U64 -> UInt64.eq_mask a b
  | U128 -> UInt128.eq_mask a b

let neq_mask #t #l a b =
  lognot (eq_mask #t #l a b)

let gte_mask #t #l a b =
  match t with
  | U1 -> logor a (lognot b)
  | U8 -> UInt8.gte_mask a b
  | U16 -> UInt16.gte_mask a b
  | U32 -> UInt32.gte_mask a b
  | U64 -> UInt64.gte_mask a b
  | U128 -> UInt128.gte_mask a b

let lt_mask #t #l a b =
  lognot (gte_mask #t #l a b)

let gt_mask #t #l a b =
  logand (gte_mask #t #l a b) (neq_mask #t #l a b)

let lte_mask #t #l a b =
  logor (lt_mask #t #l a b) (eq_mask #t #l a b)

#set-options "--z3rlimit 10 --max_fuel 0 --max_ifuel 0"

private
val mod_mask_value: #t:inttype -> #l:secrecy_level -> m:shiftval t ->
  Lemma (uint_v (mod_mask #t #l m) == pow2 (uint_v m) - 1)

let mod_mask_value #t #l m =
  admit();
  if uint_v m > 0 then begin
    let m = uint_v m in
    pow2_lt_compat (bits t) m;
    small_modulo_lemma_1 (pow2 m) (pow2 (bits t));
    assert (FStar.Mul.(1 * pow2 m) == pow2 m);
    UInt.shift_left_value_lemma #(bits t) 1 m
  end

let mod_mask_lemma #t #l a m =
  admit();
  mod_mask_value #t #l m;
  if uint_v m = 0 then
    UInt.logand_lemma_1 #(bits t) (uint_v a)
  else
    UInt.logand_mask #(bits t) (uint_v a) (uint_v m)

#reset-options "--z3rlimit 100"

(* defined in .fsti: notations +^, -^, ...*)

let nat_mod_v #m x = x

let div #t x y =
  match t with
  | U1  -> UInt8.div x y
  | U8  -> UInt8.div x y
  | U16 -> UInt16.div x y
  | U32 -> UInt32.div x y
  | U64 -> UInt64.div x y

let mod #t x y =
  match t with
  | U1  -> UInt8.rem x y
  | U8  -> UInt8.rem x y
  | U16 -> UInt16.rem x y
  | U32 -> UInt32.rem x y
  | U64 -> UInt64.rem x y

let eq #t x y =
  match t with
  | U1  -> UInt8.eq x y
  | U8  -> UInt8.eq x y
  | U16 -> UInt16.eq x y
  | U32 -> UInt32.eq x y
  | U64 -> UInt64.eq x y
  | U128 -> UInt128.eq x y

let ne #t x y =
  match t with
  | U1  -> not (UInt8.eq x y)
  | U8  -> not (UInt8.eq x y)
  | U16 -> not (UInt16.eq x y)
  | U32 -> not (UInt32.eq x y)
  | U64 -> not (UInt64.eq x y)
  | U128 -> not (UInt128.eq x y)

let lt #t x y =
  match t with
  | U1  -> UInt8.lt x y
  | U8  -> UInt8.lt x y
  | U16 -> UInt16.lt x y
  | U32 -> UInt32.lt x y
  | U64 -> UInt64.lt x y
  | U128 -> UInt128.lt x y

let lte #t x y =
  match t with
  | U1  -> UInt8.lte x y
  | U8  -> UInt8.lte x y
  | U16 -> UInt16.lte x y
  | U32 -> UInt32.lte x y
  | U64 -> UInt64.lte x y
  | U128 -> UInt128.lte x y

let gt #t x y =
  match t with
  | U1  -> UInt8.gt x y
  | U8  -> UInt8.gt x y
  | U16 -> UInt16.gt x y
  | U32 -> UInt32.gt x y
  | U64 -> UInt64.gt x y
  | U128 -> UInt128.gt x y

let gte #t x y =
  match t with
  | U1  -> UInt8.gte x y
  | U8  -> UInt8.gte x y
  | U16 -> UInt16.gte x y
  | U32 -> UInt32.gte x y
  | U64 -> UInt64.gte x y
  | U128 -> UInt128.gte x y


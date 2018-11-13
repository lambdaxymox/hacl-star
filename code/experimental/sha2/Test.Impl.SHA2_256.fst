module Test.Impl.SHA2_256

open FStar.Mul
open FStar.HyperStack
open FStar.HyperStack.ST

open LowStar.Buffer

open Lib.IntTypes
open Lib.Buffer
open Lib.ByteBuffer
open Lib.LoopCombinators
open Lib.Print


module Spec = Spec.SHA2

module Hash = Hacl.SHA2_256

inline_for_extraction let size_hash: size_nat = 32

///
/// Test 1
///

inline_for_extraction let test1_size_plaintext = 3ul
let test1_plaintext: b:lbytes (v test1_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [ 0x61; 0x62; 0x63 ])
  in
  assert_norm (List.Tot.length l == 3);
  createL_global l


let test1_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xba; 0x78; 0x16; 0xbf; 0x8f; 0x01; 0xcf; 0xea;
      0x41; 0x41; 0x40; 0xde; 0x5d; 0xae; 0x22; 0x23;
      0xb0; 0x03; 0x61; 0xa3; 0x96; 0x17; 0x7a; 0x9c;
      0xb4; 0x10; 0xff; 0x61; 0xf2; 0x00; 0x15; 0xad
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

///
/// Test 2
///

inline_for_extraction let test2_size_plaintext = 0ul
let test2_plaintext: b:lbytes (v test2_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8
    [ ])
  in
  assert_norm (List.Tot.length l == 0);
  createL_global l

let test2_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xe3; 0xb0; 0xc4; 0x42; 0x98; 0xfc; 0x1c; 0x14;
      0x9a; 0xfb; 0xf4; 0xc8; 0x99; 0x6f; 0xb9; 0x24;
      0x27; 0xae; 0x41; 0xe4; 0x64; 0x9b; 0x93; 0x4c;
      0xa4; 0x95; 0x99; 0x1b; 0x78; 0x52; 0xb8; 0x55
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l


///
/// Test 3
///

inline_for_extraction let test3_size_plaintext = 56ul
let test3_plaintext: b:lbytes (v test3_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x61; 0x62; 0x63; 0x64; 0x62; 0x63; 0x64; 0x65;
      0x63; 0x64; 0x65; 0x66; 0x64; 0x65; 0x66; 0x67;
      0x65; 0x66; 0x67; 0x68; 0x66; 0x67; 0x68; 0x69;
      0x67; 0x68; 0x69; 0x6a; 0x68; 0x69; 0x6a; 0x6b;
      0x69; 0x6a; 0x6b; 0x6c; 0x6a; 0x6b; 0x6c; 0x6d;
      0x6b; 0x6c; 0x6d; 0x6e; 0x6c; 0x6d; 0x6e; 0x6f;
      0x6d; 0x6e; 0x6f; 0x70; 0x6e; 0x6f; 0x70; 0x71
    ])
  in
  assert_norm (List.Tot.length l == 56);
  createL_global l

let test3_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x24; 0x8d; 0x6a; 0x61; 0xd2; 0x06; 0x38; 0xb8;
      0xe5; 0xc0; 0x26; 0x93; 0x0c; 0x3e; 0x60; 0x39;
      0xa3; 0x3c; 0xe4; 0x59; 0x64; 0xff; 0x21; 0x67;
      0xf6; 0xec; 0xed; 0xd4; 0x19; 0xdb; 0x06; 0xc1
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

///
/// Test 4
///

inline_for_extraction let test4_size_plaintext = 112ul
let test4_plaintext: b:lbytes (v test4_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x61; 0x62; 0x63; 0x64; 0x65; 0x66; 0x67; 0x68;
      0x62; 0x63; 0x64; 0x65; 0x66; 0x67; 0x68; 0x69;
      0x63; 0x64; 0x65; 0x66; 0x67; 0x68; 0x69; 0x6a;
      0x64; 0x65; 0x66; 0x67; 0x68; 0x69; 0x6a; 0x6b;
      0x65; 0x66; 0x67; 0x68; 0x69; 0x6a; 0x6b; 0x6c;
      0x66; 0x67; 0x68; 0x69; 0x6a; 0x6b; 0x6c; 0x6d;
      0x67; 0x68; 0x69; 0x6a; 0x6b; 0x6c; 0x6d; 0x6e;
      0x68; 0x69; 0x6a; 0x6b; 0x6c; 0x6d; 0x6e; 0x6f;
      0x69; 0x6a; 0x6b; 0x6c; 0x6d; 0x6e; 0x6f; 0x70;
      0x6a; 0x6b; 0x6c; 0x6d; 0x6e; 0x6f; 0x70; 0x71;
      0x6b; 0x6c; 0x6d; 0x6e; 0x6f; 0x70; 0x71; 0x72;
      0x6c; 0x6d; 0x6e; 0x6f; 0x70; 0x71; 0x72; 0x73;
      0x6d; 0x6e; 0x6f; 0x70; 0x71; 0x72; 0x73; 0x74;
      0x6e; 0x6f; 0x70; 0x71; 0x72; 0x73; 0x74; 0x75
    ])
  in
  assert_norm (List.Tot.length l == 112);
  createL_global l

let test4_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xcf; 0x5b; 0x16; 0xa7; 0x78; 0xaf; 0x83; 0x80;
      0x03; 0x6c; 0xe5; 0x9e; 0x7b; 0x04; 0x92; 0x37;
      0x0b; 0x24; 0x9b; 0x11; 0xe8; 0xf0; 0x7a; 0x51;
      0xaf; 0xac; 0x45; 0x03; 0x7a; 0xfe; 0xe9; 0xd1
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

///
/// Test 5
///

let test5_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xcd; 0xc7; 0x6e; 0x5c; 0x99; 0x14; 0xfb; 0x92;
      0x81; 0xa1; 0xc7; 0xe2; 0x84; 0xd7; 0x3e; 0x67;
      0xf1; 0x80; 0x9a; 0x48; 0xa4; 0x97; 0x20; 0x0e;
      0x04; 0x6d; 0x39; 0xcc; 0xc7; 0x11; 0x2c; 0xd0
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

///
/// Test 6
///

inline_for_extraction let test6_size_plaintext = 64ul
let test6_plaintext: b:lbytes (v test6_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x61; 0x62; 0x63; 0x64; 0x65; 0x66; 0x67; 0x68;
      0x62; 0x63; 0x64; 0x65; 0x66; 0x67; 0x68; 0x69;
      0x63; 0x64; 0x65; 0x66; 0x67; 0x68; 0x69; 0x6a;
      0x64; 0x65; 0x66; 0x67; 0x68; 0x69; 0x6a; 0x6b;
      0x65; 0x66; 0x67; 0x68; 0x69; 0x6a; 0x6b; 0x6c;
      0x66; 0x67; 0x68; 0x69; 0x6a; 0x6b; 0x6c; 0x6d;
      0x67; 0x68; 0x69; 0x6a; 0x6b; 0x6c; 0x6d; 0x6e;
      0x68; 0x69; 0x6a; 0x6b; 0x6c; 0x6d; 0x6e; 0x6f
    ])
  in
  assert_norm (List.Tot.length l == 64);
  createL_global l

let test6_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x50; 0xe7; 0x2a; 0x0e; 0x26; 0x44; 0x2f; 0xe2;
      0x55; 0x2d; 0xc3; 0x93; 0x8a; 0xc5; 0x86; 0x58;
      0x22; 0x8c; 0x0c; 0xbf; 0xb1; 0xd2; 0xca; 0x87;
      0x2a; 0xe4; 0x35; 0x26; 0x6f; 0xcd; 0x05; 0x5e
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

///
/// Main
///

val main: unit -> St C.exit_code
let main () =

  C.String.print (C.String.of_literal "TEST 1. \n");
  let result = create #_ #size_hash (size size_hash) (u8 0x00) in
  Hacl.SHA2_256.hash result test1_plaintext test1_size_plaintext;
  let r1 = result_compare_display (size size_hash) result test1_expected in


  C.String.print (C.String.of_literal "TEST 2. \n");
  let result2 = create #_ #size_hash (size size_hash) (u8 0x00) in
  Hacl.SHA2_256.hash result2 test2_plaintext test2_size_plaintext;
  let r2 = result_compare_display (size size_hash) result2 test2_expected in

  C.String.print (C.String.of_literal "TEST 3. \n");
  let result3 = create #_ #size_hash (size size_hash) (u8 0x00) in
  Hacl.SHA2_256.hash result3 test3_plaintext test3_size_plaintext;
  let r3 = result_compare_display (size size_hash) result3 test3_expected in

  C.String.print (C.String.of_literal "TEST 4. \n");
  let result4 = create #_ #size_hash (size size_hash) (u8 0x00) in
  Hacl.SHA2_256.hash result4 test4_plaintext test4_size_plaintext;
  let r4 = result_compare_display (size size_hash) result4 test4_expected in

  C.String.print (C.String.of_literal "TEST 5. \n");
  let result5 = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test5_plaintext = create #uint8 #1000000 (size 1000000) (u8 0x61) in
  Hacl.SHA2_256.hash result5 test5_plaintext (size 1000000);
  let r5 = result_compare_display (size size_hash) result5 test5_expected in

  C.String.print (C.String.of_literal "TEST 6. \n");
  let result6 = create #_ #size_hash (size size_hash) (u8 0x00) in
  let state6 = create #uint32 #8 (size 8) (u32 0) in
  Hacl.SHA2_256.init state6;
  let h0 = FStar.HyperStack.ST.get () in
  loop_nospec #h0 (size 16777215) state6
  (fun i ->
    Hacl.SHA2_256.update_block state6 test6_plaintext
  );
  Hacl.SHA2_256.update_last state6 (16777215ul *. test6_size_plaintext) test6_plaintext test6_size_plaintext;
  Hacl.SHA2_256.finish result6 state6;
  let r6 = result_compare_display (size size_hash) result6 test6_expected in

  if r1 && r2 && r3 && r4 && r5 && r6 then begin
    C.String.print (C.String.of_literal "Composite Result: Success !\n");
    C.EXIT_SUCCESS end
  else begin
    C.String.print (C.String.of_literal "Composite Result: Failure !\n");
    C.EXIT_FAILURE end

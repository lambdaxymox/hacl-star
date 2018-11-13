module Test.Impl.HMAC_SHA2_256

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

inline_for_extraction let size_hash: size_nat= 32

///
/// Test 1
///

inline_for_extraction let test1_size_plaintext = 8ul
let test1_plaintext: b:lbytes (v test1_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x48; 0x69; 0x20; 0x54; 0x68; 0x65; 0x72; 0x65
    ])
  in
  assert_norm (List.Tot.length l == 8);
  createL_global l


let test1_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xb0; 0x34; 0x4c; 0x61; 0xd8; 0xdb; 0x38; 0x53;
      0x5c; 0xa8; 0xaf; 0xce; 0xaf; 0x0b; 0xf1; 0x2b;
      0x88; 0x1d; 0xc2; 0x00; 0xc9; 0x83; 0x3d; 0xa7;
      0x26; 0xe9; 0x37; 0x6c; 0x2e; 0x32; 0xcf; 0xf7
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

///
/// Test 2
///

inline_for_extraction let test2_size_key = 4ul
let test2_key: b:lbytes (v test2_size_key){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x4a; 0x65; 0x66; 0x65
    ])
  in
  assert_norm (List.Tot.length l == 4);
  createL_global l


inline_for_extraction let test2_size_plaintext = 28ul
let test2_plaintext: b:lbytes (v test2_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x77; 0x68; 0x61; 0x74; 0x20; 0x64; 0x6f; 0x20;
      0x79; 0x61; 0x20; 0x77; 0x61; 0x6e; 0x74; 0x20;
      0x66; 0x6f; 0x72; 0x20; 0x6e; 0x6f; 0x74; 0x68;
      0x69; 0x6e; 0x67; 0x3f
    ])
  in
  assert_norm (List.Tot.length l == 28);
  createL_global l


let test2_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x5b; 0xdc; 0xc1; 0x46; 0xbf; 0x60; 0x75; 0x4e;
      0x6a; 0x04; 0x24; 0x26; 0x08; 0x95; 0x75; 0xc7;
      0x5a; 0x00; 0x3f; 0x08; 0x9d; 0x27; 0x39; 0x83;
      0x9d; 0xec; 0x58; 0xb9; 0x64; 0xec; 0x38; 0x43
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l

///
/// Test 3
///

let test3_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x77; 0x3e; 0xa9; 0x1e; 0x36; 0x80; 0x0e; 0x46;
      0x85; 0x4d; 0xb8; 0xeb; 0xd0; 0x91; 0x81; 0xa7;
      0x29; 0x59; 0x09; 0x8b; 0x3e; 0xf8; 0xc1; 0x22;
      0xd9; 0x63; 0x55; 0x14; 0xce; 0xd5; 0x65; 0xfe
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l


///
/// Test 4
///

inline_for_extraction let test4_size_key = 25ul
let test4_key: b:lbytes (v test4_size_key){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x01; 0x02; 0x03; 0x04; 0x05; 0x06; 0x07; 0x08;
      0x09; 0x0a; 0x0b; 0x0c; 0x0d; 0x0e; 0x0f; 0x10;
      0x11; 0x12; 0x13; 0x14; 0x15; 0x16; 0x17; 0x18;
      0x19
    ])
  in
  assert_norm (List.Tot.length l == 25);
  createL_global l

let test4_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x82; 0x55; 0x8a; 0x38; 0x9a; 0x44; 0x3c; 0x0e;
      0xa4; 0xcc; 0x81; 0x98; 0x99; 0xf2; 0x08; 0x3a;
      0x85; 0xf0; 0xfa; 0xa3; 0xe5; 0x78; 0xf8; 0x07;
      0x7a; 0x2e; 0x3f; 0xf4; 0x67; 0x29; 0x66; 0x5b
    ])
  in
  assert_norm (List.Tot.length l == 32);
  createL_global l


///
/// Test 5
///

inline_for_extraction let test5_size_plaintext = 20ul
let test5_plaintext: b:lbytes (v test5_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x54; 0x65; 0x73; 0x74; 0x20; 0x57; 0x69; 0x74;
      0x68; 0x20; 0x54; 0x72; 0x75; 0x6e; 0x63; 0x61;
      0x74; 0x69; 0x6f; 0x6e
    ])
  in
  assert_norm (List.Tot.length l == 20);
  createL_global l


let test5_expected: b:lbytes 16 =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0xa3; 0xb6; 0x16; 0x74; 0x73; 0x10; 0x0e; 0xe0;
      0x6e; 0x0c; 0x79; 0x6c; 0x29; 0x55; 0x55; 0x2b
    ])
  in
  assert_norm (List.Tot.length l == 16);
  createL_global l

///
/// Test 6
///

inline_for_extraction let test6_size_plaintext = 54ul
let test6_plaintext: b:lbytes (v test6_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x54; 0x65; 0x73; 0x74; 0x20; 0x55; 0x73; 0x69;
      0x6e; 0x67; 0x20; 0x4c; 0x61; 0x72; 0x67; 0x65;
      0x72; 0x20; 0x54; 0x68; 0x61; 0x6e; 0x20; 0x42;
      0x6c; 0x6f; 0x63; 0x6b; 0x2d; 0x53; 0x69; 0x7a;
      0x65; 0x20; 0x4b; 0x65; 0x79; 0x20; 0x2d; 0x20;
      0x48; 0x61; 0x73; 0x68; 0x20; 0x4b; 0x65; 0x79;
      0x20; 0x46; 0x69; 0x72; 0x73; 0x74
    ])
  in
  assert_norm (List.Tot.length l == 54);
  createL_global l


let test6_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x60; 0xe4; 0x31; 0x59; 0x1e; 0xe0; 0xb6; 0x7f;
      0x0d; 0x8a; 0x26; 0xaa; 0xcb; 0xf5; 0xb7; 0x7f;
      0x8e; 0x0b; 0xc6; 0x21; 0x37; 0x28; 0xc5; 0x14;
      0x05; 0x46; 0x04; 0x0f; 0x0e; 0xe3; 0x7f; 0x54
    ])
  in
  assert_norm (List.Tot.length l == size_hash);
  createL_global l


///
/// Test 7
///

inline_for_extraction let test7_size_plaintext = 152ul
let test7_plaintext: b:lbytes (v test7_size_plaintext){ recallable b } =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x54; 0x68; 0x69; 0x73; 0x20; 0x69; 0x73; 0x20;
      0x61; 0x20; 0x74; 0x65; 0x73; 0x74; 0x20; 0x75;
      0x73; 0x69; 0x6e; 0x67; 0x20; 0x61; 0x20; 0x6c;
      0x61; 0x72; 0x67; 0x65; 0x72; 0x20; 0x74; 0x68;
      0x61; 0x6e; 0x20; 0x62; 0x6c; 0x6f; 0x63; 0x6b;
      0x2d; 0x73; 0x69; 0x7a; 0x65; 0x20; 0x6b; 0x65;
      0x79; 0x20; 0x61; 0x6e; 0x64; 0x20; 0x61; 0x20;
      0x6c; 0x61; 0x72; 0x67; 0x65; 0x72; 0x20; 0x74;
      0x68; 0x61; 0x6e; 0x20; 0x62; 0x6c; 0x6f; 0x63;
      0x6b; 0x2d; 0x73; 0x69; 0x7a; 0x65; 0x20; 0x64;
      0x61; 0x74; 0x61; 0x2e; 0x20; 0x54; 0x68; 0x65;
      0x20; 0x6b; 0x65; 0x79; 0x20; 0x6e; 0x65; 0x65;
      0x64; 0x73; 0x20; 0x74; 0x6f; 0x20; 0x62; 0x65;
      0x20; 0x68; 0x61; 0x73; 0x68; 0x65; 0x64; 0x20;
      0x62; 0x65; 0x66; 0x6f; 0x72; 0x65; 0x20; 0x62;
      0x65; 0x69; 0x6e; 0x67; 0x20; 0x75; 0x73; 0x65;
      0x64; 0x20; 0x62; 0x79; 0x20; 0x74; 0x68; 0x65;
      0x20; 0x48; 0x4d; 0x41; 0x43; 0x20; 0x61; 0x6c;
      0x67; 0x6f; 0x72; 0x69; 0x74; 0x68; 0x6d; 0x2e
    ])
  in
  assert_norm (List.Tot.length l == 152);
  createL_global l


let test7_expected: b:lbytes size_hash =
  [@ inline_let]
  let l:list uint8 =
    normalize_term (List.Tot.map u8 [
      0x9b; 0x09; 0xff; 0xa7; 0x1b; 0x94; 0x2f; 0xcb;
      0x27; 0x63; 0x5f; 0xbc; 0xd5; 0xb0; 0xe9; 0x44;
      0xbf; 0xdc; 0x63; 0x64; 0x4f; 0x07; 0x13; 0x93;
      0x8a; 0x7f; 0x51; 0x53; 0x5c; 0x3a; 0x35; 0xe2
    ])
  in
  assert_norm (List.Tot.length l == size_hash);
  createL_global l


///
/// Main
///

val main: unit -> St C.exit_code
let main () =

  C.String.print (C.String.of_literal "TEST 1. \n");
  let test1_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test1_size_key: size_t = 20ul in
  let test1_key = create #uint8 #20 test1_size_key (u8 0x0b) in
  Hacl.HMAC_SHA2_256.hmac test1_result test1_key test1_size_key test1_plaintext test1_size_plaintext;
  let r1 = result_compare_display (size size_hash) test1_result test1_expected in


  C.String.print (C.String.of_literal "TEST 2. \n");
  let test2_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  Hacl.HMAC_SHA2_256.hmac test2_result test2_key test2_size_key test2_plaintext test2_size_plaintext;
  let r2 = result_compare_display (size size_hash) test2_result test2_expected in


  C.String.print (C.String.of_literal "TEST 3. \n");
  let test3_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test3_size_key: size_t = 20ul in
  let test3_key = create #uint8 #20 test3_size_key (u8 0xaa) in
  let test3_size_plaintext: size_t = 50ul in
  let test3_plaintext = create #uint8 #50 test3_size_plaintext (u8 0xdd) in
  Hacl.HMAC_SHA2_256.hmac test3_result test3_key test3_size_key test3_plaintext test3_size_plaintext;
  let r3 = result_compare_display (size size_hash) test3_result test3_expected in


  C.String.print (C.String.of_literal "TEST 4. \n");
  let test4_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test4_size_plaintext: size_t = 50ul in
  let test4_plaintext = create #uint8 #50 test4_size_plaintext (u8 0xcd) in
  Hacl.HMAC_SHA2_256.hmac test4_result test4_key test4_size_key test4_plaintext test4_size_plaintext;
  let r4 = result_compare_display (size size_hash) test4_result test4_expected in


  C.String.print (C.String.of_literal "TEST 5. \n");
  let test5_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test5_size_key: size_t = 20ul in
  let test5_key = create #uint8 #20 test5_size_key (u8 0x0c) in
  Hacl.HMAC_SHA2_256.hmac test5_result test5_key test5_size_key test5_plaintext test5_size_plaintext;
  let r5 = result_compare_display (size 16) test5_result test5_expected in


  C.String.print (C.String.of_literal "TEST 6. \n");
  let test6_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test6_size_key: size_t = 131ul in
  let test6_key = create #uint8 #131 test6_size_key (u8 0xaa) in
  Hacl.HMAC_SHA2_256.hmac test6_result test6_key test6_size_key test6_plaintext test6_size_plaintext;
  let r6 = result_compare_display (size size_hash) test6_result test6_expected in


  C.String.print (C.String.of_literal "TEST 7. \n");
  let test7_result = create #_ #size_hash (size size_hash) (u8 0x00) in
  let test7_size_key: size_t = 131ul in
  let test7_key = create #uint8 #131 test7_size_key (u8 0xaa) in
  Hacl.HMAC_SHA2_256.hmac test7_result test7_key test7_size_key test7_plaintext test7_size_plaintext;
  let r7 = result_compare_display (size size_hash) test7_result test7_expected in

  if r1 && r2 && r3 && r4 && r5 && r6 && r7 then begin
    C.String.print (C.String.of_literal "Composite Result: Success !\n");
    C.EXIT_SUCCESS end
  else begin
    C.String.print (C.String.of_literal "Composite Result: Failure !\n");
    C.EXIT_FAILURE end

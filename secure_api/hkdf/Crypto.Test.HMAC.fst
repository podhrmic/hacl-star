module Crypto.Test.HMAC

open FStar.HyperStack.All

open FStar.UInt32
open FStar.Ghost
open FStar.Buffer

module ST = FStar.HyperStack.ST
module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open Crypto.HMAC

#set-options "--lax"

val compare_and_print: Buffer.buffer UInt8.t -> Buffer.buffer UInt8.t -> UInt32.t -> St unit
let compare_and_print b1 b2 len =
//  C.print_string (C.string_of_literal s);
    if Buffer.eqb b1 b2 len then
      C.print_string (C.string_of_literal "SUCCESS!\n")
    else
    begin
    C.print_string (C.string_of_literal "FAIL!\n");
    C.print_string (C.string_of_literal "Expect: ");
    C.print_bytes b1 len;
    C.print_string (C.string_of_literal "Actual: ");
    C.print_bytes b2 len
    end


(**
   Key =          0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b
                  0b0b0b0b                          (20 bytes)
   Data =         4869205468657265                  ("Hi There")
   HMAC-SHA-224 = 896fb1128abbdf196832107cd49df33f
                  47b4b1169912ba4f53684b22
   HMAC-SHA-256 = b0344c61d8db38535ca8afceaf0bf12b
                  881dc200c9833da726e9376c2e32cff7
   HMAC-SHA-384 = afd03944d84895626b0825f4ab46907f
                  15f9dadbe4101ec682aa034c7cebc59c
                  faea9ea9076ede7f4af152e8b2fa9cb6
   HMAC-SHA-512 = 87aa7cdea5ef619d4ff0b4241a1d6cb0
                  2379f4e2ce4ec2787ad0b30545e17cde
                  daa833b7d6b8a702038b274eaea3f4e4
                  be9d914eeb61f1702e696c203a126854
**)
val test_1: unit -> St unit
let test_1 () =
  let key = Buffer.createL [
    0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
    0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
    0x0buy; 0x0buy; 0x0buy; 0x0buy;
    ] in
  let keylen = 20ul in
  let data = Buffer.createL [
    0x48uy; 0x69uy; 0x20uy; 0x54uy; 0x68uy; 0x65uy; 0x72uy; 0x65uy;
    ] in
  let datalen = 8ul in
  let mac_sha256 = Buffer.create 0uy (hash_size SHA256) in
  let mac_sha384 = Buffer.create 0uy (hash_size SHA384) in
  let mac_sha512 = Buffer.create 0uy (hash_size SHA512) in
  let expected_sha256 = Buffer.createL [
    0xb0uy; 0x34uy; 0x4cuy; 0x61uy; 0xd8uy; 0xdbuy; 0x38uy; 0x53uy;
    0x5cuy; 0xa8uy; 0xafuy; 0xceuy; 0xafuy; 0x0buy; 0xf1uy; 0x2buy;
    0x88uy; 0x1duy; 0xc2uy; 0x00uy; 0xc9uy; 0x83uy; 0x3duy; 0xa7uy;
    0x26uy; 0xe9uy; 0x37uy; 0x6cuy; 0x2euy; 0x32uy; 0xcfuy; 0xf7uy; ] in
  let expected_sha384 = Buffer.createL [
    0xafuy; 0xd0uy; 0x39uy; 0x44uy; 0xd8uy; 0x48uy; 0x95uy; 0x62uy;
    0x6buy; 0x08uy; 0x25uy; 0xf4uy; 0xabuy; 0x46uy; 0x90uy; 0x7fuy;
    0x15uy; 0xf9uy; 0xdauy; 0xdbuy; 0xe4uy; 0x10uy; 0x1euy; 0xc6uy;
    0x82uy; 0xaauy; 0x03uy; 0x4cuy; 0x7cuy; 0xebuy; 0xc5uy; 0x9cuy;
    0xfauy; 0xeauy; 0x9euy; 0xa9uy; 0x07uy; 0x6euy; 0xdeuy; 0x7fuy;
    0x4auy; 0xf1uy; 0x52uy; 0xe8uy; 0xb2uy; 0xfauy; 0x9cuy; 0xb6uy ] in
  let expected_sha512 = Buffer.createL [
    0x87uy; 0xaauy; 0x7cuy; 0xdeuy; 0xa5uy; 0xefuy; 0x61uy; 0x9duy;
    0x4fuy; 0xf0uy; 0xb4uy; 0x24uy; 0x1auy; 0x1duy; 0x6cuy; 0xb0uy;
    0x23uy; 0x79uy; 0xf4uy; 0xe2uy; 0xceuy; 0x4euy; 0xc2uy; 0x78uy;
    0x7auy; 0xd0uy; 0xb3uy; 0x05uy; 0x45uy; 0xe1uy; 0x7cuy; 0xdeuy;
    0xdauy; 0xa8uy; 0x33uy; 0xb7uy; 0xd6uy; 0xb8uy; 0xa7uy; 0x02uy;
    0x03uy; 0x8buy; 0x27uy; 0x4euy; 0xaeuy; 0xa3uy; 0xf4uy; 0xe4uy;
    0xbeuy; 0x9duy; 0x91uy; 0x4euy; 0xebuy; 0x61uy; 0xf1uy; 0x70uy;
    0x2euy; 0x69uy; 0x6cuy; 0x20uy; 0x3auy; 0x12uy; 0x68uy; 0x54uy; ] in

  C.print_string (C.string_of_literal "HMAC-SHA-256 Test 1: ");
  hmac SHA256 mac_sha256 key keylen data datalen;
  compare_and_print expected_sha256 mac_sha256 32ul;

  C.print_string (C.string_of_literal "HMAC-SHA-384 Test 1: ");
  hmac SHA384 mac_sha384 key keylen data datalen;
  compare_and_print expected_sha384 mac_sha384 48ul;

  C.print_string (C.string_of_literal "HMAC-SHA-512 Test 1: ");
  hmac SHA512 mac_sha512 key keylen data datalen;
  compare_and_print expected_sha512 mac_sha512 64ul


val main: unit -> St FStar.Int32.t
let main () =
  test_1 ();
  C.exit_success

let _ = main ()

module Spec.Test.HMAC.SHA2_512

open FStar.HyperStack.ST

open Spec.HMAC.SHA2_512

module Hash = Spec.SHA2_512

type test_vector = {
  key : k:bytes{Seq.length k < Hash.max_input_len_8};
  data: d:bytes{Seq.length d + Hash.size_block < Hash.max_input_len_8};
  mac : m:bytes{Seq.length m == Hash.size_hash}
}

(**
   Test Case 1 (https://tools.ietf.org/html/rfc4231#section-4.2)
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
let test1 =
  let key  = [
    0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
    0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy; 0x0buy;
    0x0buy; 0x0buy; 0x0buy; 0x0buy
  ] in
  let data = [
    0x48uy; 0x69uy; 0x20uy; 0x54uy; 0x68uy; 0x65uy; 0x72uy; 0x65uy
  ] in
  let mac  = [
    0x87uy; 0xaauy; 0x7cuy; 0xdeuy; 0xa5uy; 0xefuy; 0x61uy; 0x9duy;
    0x4fuy; 0xf0uy; 0xb4uy; 0x24uy; 0x1auy; 0x1duy; 0x6cuy; 0xb0uy;
    0x23uy; 0x79uy; 0xf4uy; 0xe2uy; 0xceuy; 0x4euy; 0xc2uy; 0x78uy;
    0x7auy; 0xd0uy; 0xb3uy; 0x05uy; 0x45uy; 0xe1uy; 0x7cuy; 0xdeuy;
    0xdauy; 0xa8uy; 0x33uy; 0xb7uy; 0xd6uy; 0xb8uy; 0xa7uy; 0x02uy;
    0x03uy; 0x8buy; 0x27uy; 0x4euy; 0xaeuy; 0xa3uy; 0xf4uy; 0xe4uy;
    0xbeuy; 0x9duy; 0x91uy; 0x4euy; 0xebuy; 0x61uy; 0xf1uy; 0x70uy;
    0x2euy; 0x69uy; 0x6cuy; 0x20uy; 0x3auy; 0x12uy; 0x68uy; 0x54uy;
  ] in
  assert_norm (List.Tot.length key < Hash.max_input_len_8);
  assert_norm (List.Tot.length data + Hash.size_block < Hash.max_input_len_8);
  assert_norm (List.Tot.length mac == Hash.size_hash);
  { key = Seq.createL key; data = Seq.createL data; mac = Seq.createL mac }

(**
   Test Case 2 (https://tools.ietf.org/html/rfc4231#section-4.3)

   Test with a key shorter than the length of the HMAC output.

   Key =          4a656665                          ("Jefe")
   Data =         7768617420646f2079612077616e7420  ("what do ya want ")
                  666f72206e6f7468696e673f          ("for nothing?")

   HMAC-SHA-224 = a30e01098bc6dbbf45690f3a7e9e6d0f
                  8bbea2a39e6148008fd05e44
   HMAC-SHA-256 = 5bdcc146bf60754e6a042426089575c7
                  5a003f089d2739839dec58b964ec3843
   HMAC-SHA-384 = af45d2e376484031617f78d2b58a6b1b
                  9c7ef464f5a01b47e42ec3736322445e
                  8e2240ca5e69e2c78b3239ecfab21649
   HMAC-SHA-512 = 164b7a7bfcf819e2e395fbe73b56e0a3
                  87bd64222e831fd610270cd7ea250554
                  9758bf75c05a994a6d034f65f8f0e6fd
                  caeab1a34d4a6b4b636e070a38bce737
**)
let test2 =
  let key  = [
    0x4auy; 0x65uy; 0x66uy; 0x65uy
  ] in
  let data = [
    0x77uy; 0x68uy; 0x61uy; 0x74uy; 0x20uy; 0x64uy; 0x6fuy; 0x20uy;
    0x79uy; 0x61uy; 0x20uy; 0x77uy; 0x61uy; 0x6euy; 0x74uy; 0x20uy;
    0x66uy; 0x6fuy; 0x72uy; 0x20uy; 0x6euy; 0x6fuy; 0x74uy; 0x68uy;
    0x69uy; 0x6euy; 0x67uy; 0x3fuy
  ] in
  let mac  = [
    0x16uy; 0x4buy; 0x7auy; 0x7buy; 0xfcuy; 0xf8uy; 0x19uy; 0xe2uy;
    0xe3uy; 0x95uy; 0xfbuy; 0xe7uy; 0x3buy; 0x56uy; 0xe0uy; 0xa3uy;
    0x87uy; 0xbduy; 0x64uy; 0x22uy; 0x2euy; 0x83uy; 0x1fuy; 0xd6uy;
    0x10uy; 0x27uy; 0x0cuy; 0xd7uy; 0xeauy; 0x25uy; 0x05uy; 0x54uy;
    0x97uy; 0x58uy; 0xbfuy; 0x75uy; 0xc0uy; 0x5auy; 0x99uy; 0x4auy;
    0x6duy; 0x03uy; 0x4fuy; 0x65uy; 0xf8uy; 0xf0uy; 0xe6uy; 0xfduy;
    0xcauy; 0xeauy; 0xb1uy; 0xa3uy; 0x4duy; 0x4auy; 0x6buy; 0x4buy;
    0x63uy; 0x6euy; 0x07uy; 0x0auy; 0x38uy; 0xbcuy; 0xe7uy; 0x37uy;
  ] in
  assert_norm (List.Tot.length key < Hash.max_input_len_8);
  assert_norm (List.Tot.length data + Hash.size_block < Hash.max_input_len_8);
  assert_norm (List.Tot.length mac == Hash.size_hash);
  { key = Seq.createL key; data = Seq.createL data; mac = Seq.createL mac }

(**
   Test Case 3 (https://tools.ietf.org/html/rfc4231#section-4.4)

   Test with a combined length of key and data that is larger than 64
   bytes (= block-size of SHA-224 and SHA-256).

   Key            aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaa                          (20 bytes)
   Data =         dddddddddddddddddddddddddddddddd
                  dddddddddddddddddddddddddddddddd
                  dddddddddddddddddddddddddddddddd
                  dddd                              (50 bytes)

   HMAC-SHA-224 = 7fb3cb3588c6c1f6ffa9694d7d6ad264
                  9365b0c1f65d69d1ec8333ea
   HMAC-SHA-256 = 773ea91e36800e46854db8ebd09181a7
                  2959098b3ef8c122d9635514ced565fe
   HMAC-SHA-384 = 88062608d3e6ad8a0aa2ace014c8a86f
                  0aa635d947ac9febe83ef4e55966144b
                  2a5ab39dc13814b94e3ab6e101a34f27
   HMAC-SHA-512 = fa73b0089d56a284efb0f0756c890be9
                  b1b5dbdd8ee81a3655f83e33b2279d39
                  bf3e848279a722c806b485a47e67c807
                  b946a337bee8942674278859e13292fb
**)
let test3 =
  let key  = [
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy
  ] in
  let data = [
    0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
    0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
    0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
    0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
    0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
    0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy; 0xdduy;
    0xdduy; 0xdduy
  ] in
  let mac  = [
    0xfauy; 0x73uy; 0xb0uy; 0x08uy; 0x9duy; 0x56uy; 0xa2uy; 0x84uy;
    0xefuy; 0xb0uy; 0xf0uy; 0x75uy; 0x6cuy; 0x89uy; 0x0buy; 0xe9uy;
    0xb1uy; 0xb5uy; 0xdbuy; 0xdduy; 0x8euy; 0xe8uy; 0x1auy; 0x36uy;
    0x55uy; 0xf8uy; 0x3euy; 0x33uy; 0xb2uy; 0x27uy; 0x9duy; 0x39uy;
    0xbfuy; 0x3euy; 0x84uy; 0x82uy; 0x79uy; 0xa7uy; 0x22uy; 0xc8uy;
    0x06uy; 0xb4uy; 0x85uy; 0xa4uy; 0x7euy; 0x67uy; 0xc8uy; 0x07uy;
    0xb9uy; 0x46uy; 0xa3uy; 0x37uy; 0xbeuy; 0xe8uy; 0x94uy; 0x26uy;
    0x74uy; 0x27uy; 0x88uy; 0x59uy; 0xe1uy; 0x32uy; 0x92uy; 0xfbuy;
  ] in
  assert_norm (List.Tot.length key < Hash.max_input_len_8);
  assert_norm (List.Tot.length data + Hash.size_block < Hash.max_input_len_8);
  assert_norm (List.Tot.length mac == Hash.size_hash);
  { key = Seq.createL key; data = Seq.createL data; mac = Seq.createL mac }

(**
   Test Case 4 (https://tools.ietf.org/html/rfc4231#section-4.5)

   Test with a combined length of key and data that is larger than 64
   bytes (= block-size of SHA-224 and SHA-256).

   Key =          0102030405060708090a0b0c0d0e0f10
                  111213141516171819                (25 bytes)
   Data =         cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
                  cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
                  cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd
                  cdcd                              (50 bytes)

   HMAC-SHA-224 = 6c11506874013cac6a2abc1bb382627c
                  ec6a90d86efc012de7afec5a
   HMAC-SHA-256 = 82558a389a443c0ea4cc819899f2083a
                  85f0faa3e578f8077a2e3ff46729665b
   HMAC-SHA-384 = 3e8a69b7783c25851933ab6290af6ca7
                  7a9981480850009cc5577c6e1f573b4e
                  6801dd23c4a7d679ccf8a386c674cffb
   HMAC-SHA-512 = b0ba465637458c6990e5a8c5f61d4af7
                  e576d97ff94b872de76f8050361ee3db
                  a91ca5c11aa25eb4d679275cc5788063
                  a5f19741120c4f2de2adebeb10a298dd
**)
let test4 =
  let key  = [
    0x01uy; 0x02uy; 0x03uy; 0x04uy; 0x05uy; 0x06uy; 0x07uy; 0x08uy;
    0x09uy; 0x0auy; 0x0buy; 0x0cuy; 0x0duy; 0x0euy; 0x0fuy; 0x10uy;
    0x11uy; 0x12uy; 0x13uy; 0x14uy; 0x15uy; 0x16uy; 0x17uy; 0x18uy;
    0x19uy
  ] in
  let data = [
    0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
    0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
    0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
    0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
    0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
    0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy; 0xcduy;
    0xcduy; 0xcduy
  ] in
  let mac  = [
    0xb0uy; 0xbauy; 0x46uy; 0x56uy; 0x37uy; 0x45uy; 0x8cuy; 0x69uy;
    0x90uy; 0xe5uy; 0xa8uy; 0xc5uy; 0xf6uy; 0x1duy; 0x4auy; 0xf7uy;
    0xe5uy; 0x76uy; 0xd9uy; 0x7fuy; 0xf9uy; 0x4buy; 0x87uy; 0x2duy;
    0xe7uy; 0x6fuy; 0x80uy; 0x50uy; 0x36uy; 0x1euy; 0xe3uy; 0xdbuy;
    0xa9uy; 0x1cuy; 0xa5uy; 0xc1uy; 0x1auy; 0xa2uy; 0x5euy; 0xb4uy;
    0xd6uy; 0x79uy; 0x27uy; 0x5cuy; 0xc5uy; 0x78uy; 0x80uy; 0x63uy;
    0xa5uy; 0xf1uy; 0x97uy; 0x41uy; 0x12uy; 0x0cuy; 0x4fuy; 0x2duy;
    0xe2uy; 0xaduy; 0xebuy; 0xebuy; 0x10uy; 0xa2uy; 0x98uy; 0xdduy;
  ] in
  assert_norm (List.Tot.length key < Hash.max_input_len_8);
  assert_norm (List.Tot.length data + Hash.size_block < Hash.max_input_len_8);
  assert_norm (List.Tot.length mac == Hash.size_hash);
  { key = Seq.createL key; data = Seq.createL data; mac = Seq.createL mac }

(**
   Test Case 5 (https://tools.ietf.org/html/rfc4231#section-4.6)

   Test with a truncation of output to 128 bits.

   Key =          0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
                  0c0c0c0c                          (20 bytes)
   Data =         546573742057697468205472756e6361  ("Test With Trunca")
                  74696f6e                          ("tion")

   HMAC-SHA-224 = 0e2aea68a90c8d37c988bcdb9fca6fa8
   HMAC-SHA-256 = a3b6167473100ee06e0c796c2955552b
   HMAC-SHA-384 = 3abf34c3503b2a23a46efc619baef897
   HMAC-SHA-512 = 415fad6271580a531d4179bc891d87a6
**)
let test5 =
  let key  = [
    0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
    0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy;
    0x0cuy; 0x0cuy; 0x0cuy; 0x0cuy
  ] in
  let data = [
    0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x57uy; 0x69uy; 0x74uy;
    0x68uy; 0x20uy; 0x54uy; 0x72uy; 0x75uy; 0x6euy; 0x63uy; 0x61uy;
    0x74uy; 0x69uy; 0x6fuy; 0x6euy
  ] in
  let mac  = [
    0x41uy; 0x5fuy; 0xaduy; 0x62uy; 0x71uy; 0x58uy; 0x0auy; 0x53uy;
    0x1duy; 0x41uy; 0x79uy; 0xbcuy; 0x89uy; 0x1duy; 0x87uy; 0xa6uy;
  ] in
  assert_norm (List.Tot.length key < Hash.max_input_len_8);
  assert_norm (List.Tot.length data + Hash.size_block < Hash.max_input_len_8);
  assert_norm (List.Tot.length mac == Hash.size_hash);
  { key = Seq.createL key; data = Seq.createL data; mac = Seq.createL mac }

(**
   Test Case 6 (https://tools.ietf.org/html/rfc4231#section-4.7)

   Test with a key larger than 128 bytes (= block-size of SHA-384 and
   SHA-512).

   Key =          aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaa                            (131 bytes)
   Data =         54657374205573696e67204c61726765  ("Test Using Large")
                  72205468616e20426c6f636b2d53697a  ("r Than Block-Siz")
                  65204b6579202d2048617368204b6579  ("e Key - Hash Key")
                  204669727374                      (" First")

   HMAC-SHA-224 = 95e9a0db962095adaebe9b2d6f0dbce2
                  d499f112f2d2b7273fa6870e
   HMAC-SHA-256 = 60e431591ee0b67f0d8a26aacbf5b77f
                  8e0bc6213728c5140546040f0ee37f54
   HMAC-SHA-384 = 4ece084485813e9088d2c63a041bc5b4
                  4f9ef1012a2b588f3cd11f05033ac4c6
                  0c2ef6ab4030fe8296248df163f44952
   HMAC-SHA-512 = 80b24263c7c1a3ebb71493c1dd7be8b4
                  9b46d1f41b4aeec1121b013783f8f352
                  6b56d037e05f2598bd0fd2215d6a1e52
                  95e64f73f63f0aec8b915a985d786598
**)
let test6 =
  let key  = [
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy
  ] in
  let data = [
    0x54uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x55uy; 0x73uy; 0x69uy;
    0x6euy; 0x67uy; 0x20uy; 0x4cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy;
    0x72uy; 0x20uy; 0x54uy; 0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x42uy;
    0x6cuy; 0x6fuy; 0x63uy; 0x6buy; 0x2duy; 0x53uy; 0x69uy; 0x7auy;
    0x65uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy; 0x20uy; 0x2duy; 0x20uy;
    0x48uy; 0x61uy; 0x73uy; 0x68uy; 0x20uy; 0x4buy; 0x65uy; 0x79uy;
    0x20uy; 0x46uy; 0x69uy; 0x72uy; 0x73uy; 0x74uy
  ] in
  let mac  = [
    0x80uy; 0xb2uy; 0x42uy; 0x63uy; 0xc7uy; 0xc1uy; 0xa3uy; 0xebuy;
    0xb7uy; 0x14uy; 0x93uy; 0xc1uy; 0xdduy; 0x7buy; 0xe8uy; 0xb4uy;
    0x9buy; 0x46uy; 0xd1uy; 0xf4uy; 0x1buy; 0x4auy; 0xeeuy; 0xc1uy;
    0x12uy; 0x1buy; 0x01uy; 0x37uy; 0x83uy; 0xf8uy; 0xf3uy; 0x52uy;
    0x6buy; 0x56uy; 0xd0uy; 0x37uy; 0xe0uy; 0x5fuy; 0x25uy; 0x98uy;
    0xbduy; 0x0fuy; 0xd2uy; 0x21uy; 0x5duy; 0x6auy; 0x1euy; 0x52uy;
    0x95uy; 0xe6uy; 0x4fuy; 0x73uy; 0xf6uy; 0x3fuy; 0x0auy; 0xecuy;
    0x8buy; 0x91uy; 0x5auy; 0x98uy; 0x5duy; 0x78uy; 0x65uy; 0x98uy;
  ] in
  assert_norm (List.Tot.length key < Hash.max_input_len_8);
  assert_norm (List.Tot.length data + Hash.size_block < Hash.max_input_len_8);
  assert_norm (List.Tot.length mac == Hash.size_hash);
  { key = Seq.createL key; data = Seq.createL data; mac = Seq.createL mac }


(**
   Test Case 7 (https://tools.ietf.org/html/rfc4231#section-4.8)

   Test with a key and data that is larger than 128 bytes (= block-size
   of SHA-384 and SHA-512).

   Key =          aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
                  aaaaaa                            (131 bytes)
   Data =         54686973206973206120746573742075  ("This is a test u")
                  73696e672061206c6172676572207468  ("sing a larger th")
                  616e20626c6f636b2d73697a65206b65  ("an block-size ke")
                  7920616e642061206c61726765722074  ("y and a larger t")
                  68616e20626c6f636b2d73697a652064  ("han block-size d")
                  6174612e20546865206b6579206e6565  ("ata. The key nee")
                  647320746f2062652068617368656420  ("ds to be hashed ")
                  6265666f7265206265696e6720757365  ("before being use")
                  642062792074686520484d414320616c  ("d by the HMAC al")
                  676f726974686d2e                  ("gorithm.")

   HMAC-SHA-224 = 3a854166ac5d9f023f54d517d0b39dbd
                  946770db9c2b95c9f6f565d1
   HMAC-SHA-256 = 9b09ffa71b942fcb27635fbcd5b0e944
                  bfdc63644f0713938a7f51535c3a35e2
   HMAC-SHA-384 = 6617178e941f020d351e2f254e8fd32c
                  602420feb0b8fb9adccebb82461e99c5
                  a678cc31e799176d3860e6110c46523e
   HMAC-SHA-512 = e37b6a775dc87dbaa4dfa9f96e5e3ffd
                  debd71f8867289865df5a32d20cdc944
                  b6022cac3c4982b10d5eeb55c3e4de15
                  134676fb6de0446065c97440fa8c6a58
**)
let test7 =
  let key  = [
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy; 0xaauy;
    0xaauy; 0xaauy; 0xaauy
  ] in
  let data = [
    0x54uy; 0x68uy; 0x69uy; 0x73uy; 0x20uy; 0x69uy; 0x73uy; 0x20uy;
    0x61uy; 0x20uy; 0x74uy; 0x65uy; 0x73uy; 0x74uy; 0x20uy; 0x75uy;
    0x73uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x61uy; 0x20uy; 0x6cuy;
    0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy; 0x68uy;
    0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy; 0x6buy;
    0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x6buy; 0x65uy;
    0x79uy; 0x20uy; 0x61uy; 0x6euy; 0x64uy; 0x20uy; 0x61uy; 0x20uy;
    0x6cuy; 0x61uy; 0x72uy; 0x67uy; 0x65uy; 0x72uy; 0x20uy; 0x74uy;
    0x68uy; 0x61uy; 0x6euy; 0x20uy; 0x62uy; 0x6cuy; 0x6fuy; 0x63uy;
    0x6buy; 0x2duy; 0x73uy; 0x69uy; 0x7auy; 0x65uy; 0x20uy; 0x64uy;
    0x61uy; 0x74uy; 0x61uy; 0x2euy; 0x20uy; 0x54uy; 0x68uy; 0x65uy;
    0x20uy; 0x6buy; 0x65uy; 0x79uy; 0x20uy; 0x6euy; 0x65uy; 0x65uy;
    0x64uy; 0x73uy; 0x20uy; 0x74uy; 0x6fuy; 0x20uy; 0x62uy; 0x65uy;
    0x20uy; 0x68uy; 0x61uy; 0x73uy; 0x68uy; 0x65uy; 0x64uy; 0x20uy;
    0x62uy; 0x65uy; 0x66uy; 0x6fuy; 0x72uy; 0x65uy; 0x20uy; 0x62uy;
    0x65uy; 0x69uy; 0x6euy; 0x67uy; 0x20uy; 0x75uy; 0x73uy; 0x65uy;
    0x64uy; 0x20uy; 0x62uy; 0x79uy; 0x20uy; 0x74uy; 0x68uy; 0x65uy;
    0x20uy; 0x48uy; 0x4duy; 0x41uy; 0x43uy; 0x20uy; 0x61uy; 0x6cuy;
    0x67uy; 0x6fuy; 0x72uy; 0x69uy; 0x74uy; 0x68uy; 0x6duy; 0x2euy
  ] in
  let mac  = [
    0xe3uy; 0x7buy; 0x6auy; 0x77uy; 0x5duy; 0xc8uy; 0x7duy; 0xbauy;
    0xa4uy; 0xdfuy; 0xa9uy; 0xf9uy; 0x6euy; 0x5euy; 0x3fuy; 0xfduy;
    0xdeuy; 0xbduy; 0x71uy; 0xf8uy; 0x86uy; 0x72uy; 0x89uy; 0x86uy;
    0x5duy; 0xf5uy; 0xa3uy; 0x2duy; 0x20uy; 0xcduy; 0xc9uy; 0x44uy;
    0xb6uy; 0x02uy; 0x2cuy; 0xacuy; 0x3cuy; 0x49uy; 0x82uy; 0xb1uy;
    0x0duy; 0x5euy; 0xebuy; 0x55uy; 0xc3uy; 0xe4uy; 0xdeuy; 0x15uy;
    0x13uy; 0x46uy; 0x76uy; 0xfbuy; 0x6duy; 0xe0uy; 0x44uy; 0x60uy;
    0x65uy; 0xc9uy; 0x74uy; 0x40uy; 0xfauy; 0x8cuy; 0x6auy; 0x58uy;
  ] in
  assert_norm (List.Tot.length key < Hash.max_input_len_8);
  assert_norm (List.Tot.length data + Hash.size_block < Hash.max_input_len_8);
  assert_norm (List.Tot.length mac == Hash.size_hash);
  { key = Seq.createL key; data = Seq.createL data; mac = Seq.createL mac }


(** Run all test cases -- can take a while *)
let main =
  TestLib.compare_and_print "HMAC-SHA2-512 - Test 1"
    test1.mac (hmac test1.key test1.data);
  TestLib.compare_and_print "HMAC-SHA2-512 - Test 2"
    test2.mac (hmac test2.key test2.data);
  TestLib.compare_and_print "HMAC-SHA2-512 - Test 3"
    test3.mac (hmac test3.key test3.data);
  TestLib.compare_and_print "HMAC-SHA2-512 - Test 4"
    test4.mac (hmac test4.key test4.data);
  TestLib.compare_and_print "HMAC-SHA2-512 - Test 5"
    test5.mac (Seq.slice (hmac test5.key test5.data) 0 (128 / 8));
  TestLib.compare_and_print "HMAC-SHA2-512 - Test 6"
    test6.mac (hmac test6.key test6.data);
  TestLib.compare_and_print "HMAC-SHA2-512 - Test 7"
    test7.mac (hmac test7.key test7.data)

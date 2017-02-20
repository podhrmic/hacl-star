module Spec.Chacha20

open FStar.Mul
open FStar.Seq
open FStar.UInt32
open FStar.Endianness
open Spec.Lib

(* This should go elsewhere! *)

#set-options "--initial_fuel 0 --max_fuel 0 --z3rlimit 100"

// left rotation by s bits; could go elsewhere
let op_Less_Less_Less (a:UInt32.t) (s:UInt32.t {v s<32}) : Tot UInt32.t =
  (a <<^ s) |^ (a >>^ (32ul -^ s))

let keylen = 32 (* in bytes *)
let blocklen = 64  (* in bytes *)
let noncelen = 12 (* in bytes *)

type key = lbytes keylen
type block = lbytes blocklen
type nonce = lbytes noncelen
type counter = UInt.uint_t 32

// using @ as a functional substitute for ;
// internally, blocks are represented as 16 x 4-byte integers
type state = m:seq UInt32.t {length m = 16}
type idx = n:nat{n < 16}
type shuffle = state -> Tot state 

val line: idx -> idx -> idx -> s:UInt32.t {v s < 32} -> shuffle
let line a b d s m = 
  let m = upd m a (index m a +%^ index m b) in
  let m = upd m d ((index m d ^^  index m a) <<< s) in
  m

let quarter_round a b c d : shuffle = 
  line a b d 16ul @ 
  line c d b 12ul @
  line a b d 8ul @ 
  line c d b 7ul 

let column_round : shuffle = 
  quarter_round 0 4 8 12 @
  quarter_round 1 5 9 13 @
  quarter_round 2 6 10 14 @
  quarter_round 3 7 11 15

let diagonal_round : shuffle = 
  quarter_round 0 5 10 15 @
  quarter_round 1 6 11 12 @
  quarter_round 2 7 8 13 @
  quarter_round 3 4 9 14

let double_round: shuffle = 
    column_round @ diagonal_round (* 2 rounds *)

let rec rounds : shuffle = 
    iter 10 double_round (* 20 rounds *)

let chacha20_core (s:state) = 
    let s' = rounds s in
    map2 (fun x y -> x +%^ y) s s'

(* state initialization *) 

let constants = [0x61707865ul; 0x3320646eul; 0x79622d32ul; 0x6b206574ul]

let setup (k:key) (n:nonce) (c:counter): state =
  createL constants @|
  uint32s_from_le 8 k @|
  createL [UInt32.uint_to_t c] @| 
  uint32s_from_le 3 n

let chacha20_block (k:key) (n:nonce) (c:counter): block =
    let st = setup k n c in
    let st' = chacha20_core st in
    uint32s_to_le 16 st'


let chacha20_ctx: Spec.CTR.block_cipher_ctx = 
    let open Spec.CTR in
    {
    keylen = keylen;
    blocklen = blocklen;
    noncelen = noncelen;
    counterbits = 32
    }

let chacha20_cipher: Spec.CTR.block_cipher chacha20_ctx = chacha20_block

let chacha20_encrypt_bytes key nonce counter m = 
    Spec.CTR.counter_mode chacha20_ctx chacha20_cipher key nonce counter m


unfold let test_plaintext : lbytes 114 = createL [
    0x4cuy; 0x61uy; 0x64uy; 0x69uy; 0x65uy; 0x73uy; 0x20uy; 0x61uy; 
    0x6euy; 0x64uy; 0x20uy; 0x47uy; 0x65uy; 0x6euy; 0x74uy; 0x6cuy;
    0x65uy; 0x6duy; 0x65uy; 0x6euy; 0x20uy; 0x6fuy; 0x66uy; 0x20uy;
    0x74uy; 0x68uy; 0x65uy; 0x20uy; 0x63uy; 0x6cuy; 0x61uy; 0x73uy;
    0x73uy; 0x20uy; 0x6fuy; 0x66uy; 0x20uy; 0x27uy; 0x39uy; 0x39uy;
    0x3auy; 0x20uy; 0x49uy; 0x66uy; 0x20uy; 0x49uy; 0x20uy; 0x63uy;
    0x6fuy; 0x75uy; 0x6cuy; 0x64uy; 0x20uy; 0x6fuy; 0x66uy; 0x66uy;
    0x65uy; 0x72uy; 0x20uy; 0x79uy; 0x6fuy; 0x75uy; 0x20uy; 0x6fuy;
    0x6euy; 0x6cuy; 0x79uy; 0x20uy; 0x6fuy; 0x6euy; 0x65uy; 0x20uy; 
    0x74uy; 0x69uy; 0x70uy; 0x20uy; 0x66uy; 0x6fuy; 0x72uy; 0x20uy;
    0x74uy; 0x68uy; 0x65uy; 0x20uy; 0x66uy; 0x75uy; 0x74uy; 0x75uy;
    0x72uy; 0x65uy; 0x2cuy; 0x20uy; 0x73uy; 0x75uy; 0x6euy; 0x73uy;
    0x63uy; 0x72uy; 0x65uy; 0x65uy; 0x6euy; 0x20uy; 0x77uy; 0x6fuy;
    0x75uy; 0x6cuy; 0x64uy; 0x20uy; 0x62uy; 0x65uy; 0x20uy; 0x69uy;
    0x74uy; 0x2euy
]

unfold let test_ciphertext  = createL [
    0x6euy; 0x2euy; 0x35uy; 0x9auy; 0x25uy; 0x68uy; 0xf9uy; 0x80uy;
    0x41uy; 0xbauy; 0x07uy; 0x28uy; 0xdduy; 0x0duy; 0x69uy; 0x81uy;
    0xe9uy; 0x7euy; 0x7auy; 0xecuy; 0x1duy; 0x43uy; 0x60uy; 0xc2uy;
    0x0auy; 0x27uy; 0xafuy; 0xccuy; 0xfduy; 0x9fuy; 0xaeuy; 0x0buy;
    0xf9uy; 0x1buy; 0x65uy; 0xc5uy; 0x52uy; 0x47uy; 0x33uy; 0xabuy;
    0x8fuy; 0x59uy; 0x3duy; 0xabuy; 0xcduy; 0x62uy; 0xb3uy; 0x57uy;
    0x16uy; 0x39uy; 0xd6uy; 0x24uy; 0xe6uy; 0x51uy; 0x52uy; 0xabuy;
    0x8fuy; 0x53uy; 0x0cuy; 0x35uy; 0x9fuy; 0x08uy; 0x61uy; 0xd8uy;
    0x07uy; 0xcauy; 0x0duy; 0xbfuy; 0x50uy; 0x0duy; 0x6auy; 0x61uy;
    0x56uy; 0xa3uy; 0x8euy; 0x08uy; 0x8auy; 0x22uy; 0xb6uy; 0x5euy;
    0x52uy; 0xbcuy; 0x51uy; 0x4duy; 0x16uy; 0xccuy; 0xf8uy; 0x06uy;
    0x81uy; 0x8cuy; 0xe9uy; 0x1auy; 0xb7uy; 0x79uy; 0x37uy; 0x36uy;
    0x5auy; 0xf9uy; 0x0buy; 0xbfuy; 0x74uy; 0xa3uy; 0x5buy; 0xe6uy;
    0xb4uy; 0x0buy; 0x8euy; 0xeduy; 0xf2uy; 0x78uy; 0x5euy; 0x42uy;
    0x87uy; 0x4duy
]

unfold let test_key:key = createL [
    0uy;   1uy;  2uy;  3uy;  4uy;  5uy;  6uy;  7uy;
    8uy;   9uy; 10uy; 11uy; 12uy; 13uy; 14uy; 15uy;
    16uy; 17uy; 18uy; 19uy; 20uy; 21uy; 22uy; 23uy;
    24uy; 25uy; 26uy; 27uy; 28uy; 29uy; 30uy; 31uy
    ] 
unfold let test_nonce:nonce = createL [ 
    0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0uy; 0x4auy; 0uy; 0uy; 0uy; 0uy
    ] 

unfold let test_counter = 1

let test() = 
    chacha20_encrypt_bytes test_key test_nonce test_counter test_plaintext 
    = test_ciphertext
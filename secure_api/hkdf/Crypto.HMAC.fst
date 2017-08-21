(* Agile HKDF *)
module Crypto.HMAC

module ST = FStar.HyperStack.ST
open FStar.HyperStack.All

open FStar.HyperStack
open FStar.Buffer
open Buffer.Utils

module HH = FStar.HyperHeap
module HS = FStar.HyperStack

open FStar.UInt32
open Crypto.Symmetric.Bytes
open Crypto.Indexing

open C.Loops

(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64

module Spec_H256 = Spec.SHA2_256
module H256 = Hacl.Hash.SHA2_256
module Spec_H384 = Spec.SHA2_384
module H384 = Hacl.Hash.SHA2_384
module Spec_H512 = Spec.SHA2_512
module H512 = Hacl.Hash.SHA2_512

module Spec_HMAC256 = Spec.HMAC.SHA2_256
module Spec_HMAC512 = Spec.HMAC.SHA2_512


private let uint8_t  = FStar.UInt8.t
private let uint32_t = FStar.UInt32.t
private let uint32_p = Buffer.buffer uint32_t
private let uint8_p  = Buffer.buffer uint8_t
private let uint64_t = FStar.UInt64.t
private let uint64_p = Buffer.buffer uint64_t

type bytes = Seq.seq uint8_t
type lbytes (n:nat) = b:bytes{Seq.length b = n}

#set-options "--lax"

let xor_bytes_inplace a b len =
  C.Loops.in_place_map2 a b len (fun x y -> U8.logxor x y)

type alg =
  | SHA256
  | SHA384
  | SHA512

let block_size : alg -> Tot uint32_t = function
  | SHA256 -> H256.size_block
  | SHA384 -> H384.size_block
  | SHA512 -> H512.size_block

let hash_size: alg -> Tot uint32_t = function
  | SHA256 -> H256.size_hash
  | SHA384 -> H384.size_hash_final // Note that `size_hash` is 64, not 48
  | SHA512 -> H512.size_hash

inline_for_extraction let state_size: alg -> Tot uint32_t = function
  | SHA256 -> H256.size_state
  | SHA384 -> H384.size_state
  | SHA512 -> H512.size_state

noextract let max_byte_length : alg -> Tot nat = function
  | SHA256 -> Spec_H256.max_input_len_8
  | SHA384 -> Spec_H384.max_input_len_8
  | SHA512 -> Spec_H512.max_input_len_8

let correct_wrap_key (a:alg)
  (key:Seq.seq uint8_t{Seq.length key < max_byte_length a})
  (wrapped:Seq.seq uint8_t{Seq.length wrapped = v (block_size a)}) : GTot Type =
  match a with
  | SHA256 -> Spec_HMAC256.wrap_key key == wrapped
  | SHA384 -> True // Spec missing
  | SHA512 -> Spec_HMAC512.wrap_key key == wrapped

let correct_agile_hash (a:alg)
  (input:Seq.seq uint8_t{Seq.length input < max_byte_length a})
  (digest:Seq.seq uint8_t{Seq.length digest = v (hash_size a)}) : GTot Type =
  match a with
  | SHA256 -> Spec_H256.hash input == digest
  | SHA384 -> Spec_H384.hash input == digest
  | SHA512 -> Spec_H512.hash input == digest

let agile_hash (a:alg) (output:uint8_p{length output = v (hash_size a)})
  (input:uint8_p{length input < max_byte_length a /\ disjoint output input})
  (len:uint32_t{v len = length output})
  : Stack unit
  (requires fun h -> live h input /\ live h output
    /\ (as_seq h output) == Seq.create (v (hash_size a)) 0uy)
  (ensures fun h0 _ h1 -> live h1 output /\ live h1 input
    /\ modifies_1 output h0 h1
    /\ as_seq h1 input == as_seq h0 input
    /\ correct_agile_hash a (as_seq h1 input) (as_seq h1 output))
  =
  match a with
  | SHA256 -> H256.hash output input len
  | SHA384 -> H384.hash output input len
  | SHA512 -> H512.hash output input len

[@"substitute"]
val wrap_key:
  a      : alg ->
  output : uint8_p  {length output = v (block_size a)} ->
  key    : uint8_p  {disjoint output key} ->
  len    : uint32_t {v len = length key /\ v len < max_byte_length a} ->
  Stack unit
    (requires (fun h -> live h output /\ live h key /\
      (as_seq h output) == Seq.create (v (block_size a)) 0uy))
    (ensures  (fun h0 _ h1 -> live h1 output /\ live h1 key /\ live h0 output /\ live h0 key
      /\ modifies_1 output h0 h1
      /\ as_seq h0 output == Seq.create (v (block_size a)) 0uy
      /\ correct_wrap_key a (as_seq h0 key) (as_seq h1 output)))

let wrap_key a output key len =
  if len <=^ block_size a then
    Buffer.blit key 0ul output 0ul len
  else
    let nkey = Buffer.sub output 0ul (hash_size a) in
    agile_hash a nkey key len

let counter_pos: alg -> Tot uint32_t = function
  | SHA256 -> H256.pos_count_w
  | SHA384 -> H384.pos_count_w
  | SHA512 -> H512.pos_count_w

let counter_size: alg -> Tot uint32_t = function
  | SHA256 -> H256.size_count_w
  | SHA384 -> H384.size_count_w
  | SHA512 -> H512.size_count_w

let state = function
  | SHA256 -> st:uint32_p{length st = v (H256.size_state)}
  | SHA384 -> st:uint64_p{length st = v (H384.size_state)}
  | SHA512 -> st:uint64_p{length st = v (H512.size_state)}

let agile_alloc (a:alg) : Stack (st:state a)
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True)
  =
  match a with
  | SHA256 -> Buffer.create 0ul (state_size a)
  | SHA384 -> Buffer.create 0uL (state_size a)
  | SHA512 -> Buffer.create 0uL (state_size a)

let agile_init (a:alg) (st:state a) : Stack unit
   (requires fun h -> True)
   (ensures fun h0 _ h1 -> True) // live h1 st /\ modifies_1 st h0 h1)
   =
   match a with
   | SHA256 -> H256.init st
   | SHA384 -> H384.init st
   | SHA512 -> H512.init st

let agile_update (a:alg) (st:state a)
  (input:uint8_p {length input = v (block_size a)}) : Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True) // live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.update st input
  | SHA384 -> H384.update st input
  | SHA512 -> H512.update st input

let agile_update_last (a:alg) (st:state a)
  (input:uint8_p {length input = v (block_size a)})
  (len:uint32_t {v len = length input}) : Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True) //live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.update_last st input len
  | SHA384 -> H384.update_last st input (Int.Cast.uint32_to_uint64 len)
  | SHA512 -> H512.update_last st input (Int.Cast.uint32_to_uint64 len)

let agile_finish (a:alg) (st:state a)
  (hash:uint8_p {length hash = v (hash_size a)}) : Stack unit
  (requires fun h -> True)
  (ensures fun h0 _ h1 -> True) //live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.finish st hash
  | SHA384 -> H384.finish st hash
  | SHA512 -> H512.finish st hash

let agile_update_multi (a:alg) (st:state a)
  (input:uint8_p {length input % v (block_size a) = 0})
  (nblocks:uint32_t{op_Multiply (v nblocks) (v (block_size a)) = length input})
  : Stack unit (requires fun h -> True)
  (ensures fun h0 _ h1 -> True) //live h1 st /\ modifies_1 st h0 h1)
  =
  match a with
  | SHA256 -> H256.update_multi st input nblocks
  | SHA384 -> H384.update_multi st input nblocks
  | SHA512 -> H512.update_multi st input nblocks

val lemma_alloc:
  a: alg ->
  s: state a ->
  Lemma
    (requires (s == Seq.create (v (state_size a)) 0ul))
    (ensures (
      let seq_counter = Seq.slice s (U32.v (counter_pos a)) (U32.(v (counter_pos a) + v (counter_size a))) in
      let counter = Seq.index seq_counter 0 in
      U32.v counter = 0))
let lemma_alloc a s = ()

[@"substitute"]
val hmac_part1:
  a    : alg ->
  state0 : state a ->
  s2   : uint8_p {length s2 = v (block_size a)} ->
  data : uint8_p  {length data + v (block_size a) < pow2 32 /\ disjoint data s2} ->
  len  : uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h ->  live h s2 /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 s2 /\ live h0 s2
                             /\ live h1 data /\ live h0 data /\ modifies_1 s2 h0 h1
                             /\ (let hash0 = Seq.slice (as_seq h1 s2) 0 (v (hash_size a)) in
                             correct_agile_hash a (Seq.append (as_seq h0 s2) (as_seq h0 data)) hash0)))

[@"substitute"]
let hmac_part1 a state0 s2 data len =
  push_frame ();

  (* Step 3: append data to "result of step 2" *)
  (* Step 4: apply Hash to "result of step 3" *)
  let n0 = U32.div len (block_size a) in
  let r0 = U32.rem len (block_size a) in

  let blocks0 = Buffer.sub data 0ul (n0 *^ (block_size a)) in
  let last0 = Buffer.offset data (n0 *^ (block_size a)) in
  agile_init a state0;
  agile_update a state0 s2;
  agile_update_multi a state0 blocks0 n0;
  agile_update_last a state0 last0 r0;

  let hash0 = Buffer.sub s2 0ul (hash_size a) in (* Salvage memory *)
  agile_finish a state0 hash0; (* s4 = hash (s2 @| data) *)
  pop_frame ()


[@"substitute"]
val hmac_part2:
  a   : alg ->
  state1 : state a ->
  mac : uint8_p {length mac = v (hash_size a)} ->
  s5  : uint8_p {length s5 = v (block_size a) /\ disjoint s5 mac} ->
  s4  : uint8_p {length s4 = v (hash_size a) /\ disjoint s4 mac /\ disjoint s4 s5} ->
  Stack unit
        (requires (fun h -> True)) // live h mac /\ live h s5 /\ live h s4))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac))
 ///\ live h1 s5 /\ live h0 s5
 ///\ live h1 s4 /\ live h0 s4 /\ modifies_1 mac h0 h1
 ///\ (reveal_sbytes (as_seq h1 mac) == Spec_Hash.hash (Seq.append (reveal_sbytes (as_seq h0 s5)) (reveal_sbytes (as_seq h0 s4))))))

[@"substitute"]
let hmac_part2 a state1 mac s5 s4 =
  push_frame ();
  agile_init a state1;
  agile_update a state1 s5;
  agile_update_last a state1 s4 (hash_size a);
  agile_finish a state1 mac;
  pop_frame ()


val hmac_core:
  a    : alg ->
  state: state a ->
  mac  : uint8_p  {length mac = v (hash_size a)} ->
  key  : uint8_p  {length key = v (block_size a) /\ disjoint key mac} ->
  data : uint8_p  {length data + v (block_size a) < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  len  : uint32_t {length data = v len} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1))
//                             /\ (reveal_sbytes (as_seq h1 mac) == Spec.hmac_core (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)))))

(* 2017.08.20 SZ: Not extracted to memset(); why? *)
[@"substitute"]
let zero_state (a:alg) (b:state a) =
  match a with
  | SHA256 -> Buffer.fill b 0ul (state_size a)
  | SHA384 -> Buffer.fill b 0uL (state_size a)
  | SHA512 -> Buffer.fill b 0uL (state_size a)

let hmac_core a state mac key data len =
  push_frame ();

  (* Initialize constants *)
  let ipad = Buffer.create 0x36uy (block_size a) in
  let opad = Buffer.create 0x5cuy (block_size a) in

  xor_bytes_inplace ipad key (block_size a);

  hmac_part1 a state ipad data len;
  let s4 = Buffer.sub ipad 0ul (hash_size a) in (* Salvage memory *)

  (* Step 5: xor "result of step 1" with opad *)
  xor_bytes_inplace opad key (block_size a);

  (* Step 6: append "result of step 4" to "result of step 5" *)
  (* Step 7: apply H to "result of step 6" *)
  zero_state a state;
  hmac_part2 a state mac opad s4; (* s5 = opad *)

  pop_frame ()


val hmac:
  a       : alg ->
  mac     : uint8_p  {length mac = v (hash_size a)} ->
  key     : uint8_p  {length key = v (block_size a) /\ disjoint key mac} ->
  keylen  : uint32_t {v keylen = length key} ->
  data    : uint8_p  {length data + v (block_size a) < pow2 32 /\ disjoint data mac /\ disjoint data key} ->
  datalen : uint32_t {v datalen = length data} ->
  Stack unit
        (requires (fun h -> live h mac /\ live h key /\ live h data))
        (ensures  (fun h0 _ h1 -> live h1 mac /\ live h0 mac
                             /\ live h1 key /\ live h0 key
                             /\ live h1 data /\ live h0 data /\ modifies_1 mac h0 h1))
//                             /\ (reveal_sbytes (as_seq h1 mac) == Spec.hmac (reveal_sbytes (as_seq h0 key)) (reveal_sbytes (as_seq h0 data)))))

let hmac a mac key keylen data datalen =
  (*
   *  REMARK:
   *  The base type of the state buffer is parametric on the algorithm
   *  (uint32_t for SHA2-256 and uint64_t for SHA2-384 and SHA2-512).
   *  Each state allocation has to occur in its own frame for Kremlin to
   *  extract it correctly.
   *)
  match a with
  | SHA256 ->
    begin
    push_frame ();
    let st = Buffer.create 0ul (state_size a) in
    let nkey = Buffer.create 0uy (block_size a) in
    wrap_key a nkey key keylen;
    hmac_core a st mac nkey data datalen;
    pop_frame ()
    end

  | SHA384 ->
    begin
    push_frame ();
    let st = Buffer.create 0uL (state_size a) in
    let nkey = Buffer.create 0uy (block_size a) in
    wrap_key a nkey key keylen;
    hmac_core a st mac nkey data datalen;
    pop_frame ()
    end

  | SHA512 ->
    begin
    push_frame ();
    let st = Buffer.create 0uL (state_size a) in
    let nkey = Buffer.create 0uy (block_size a) in
    wrap_key a nkey key keylen;
    hmac_core a st mac nkey data datalen;
    pop_frame ()
    end

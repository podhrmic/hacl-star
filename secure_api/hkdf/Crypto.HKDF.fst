module Crypto.HKDF

module ST = FStar.HyperStack.ST

open FStar.HyperStack.All

open FStar.Mul
open FStar.Ghost
open FStar.HyperStack
open FStar.HyperStack.ST
open FStar.Buffer
open FStar.UInt32

(* Definition of aliases for modules *)
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module HMAC = Crypto.HMAC

(* Definition of base types *)
let uint8_t   = FStar.UInt8.t
let uint32_t  = FStar.UInt32.t
let uint64_t  = FStar.UInt64.t

let uint32_p = Buffer.buffer uint32_t
let uint8_p  = Buffer.buffer uint8_t

type alg = HMAC.alg

#reset-options "--z3rlimit 40 --max_fuel 0 --max_ifuel 0"


(*
 * REMARK: RFC 5869 defines the salt value as optional;
 * if not provided, it is set to a string of `hashsize` zeros.
 *
 * Internally, HMAC extends `salt` with zeros to a string of `blocksize` bytes.
 * For `salt` longer than `blocksize`, the value passed to HMAC
 * is obtained by hashing `salt` to a string of length `hashlen` (which may
 * then be expanded to `blocksize`).
 *
 * This interface (and the one in HMAC) assumes that the hashing and
 * extension of `salt` has already been done, so `saltlen` is redundant.
 *
 * 2017.08.18: SZ: I chose to kept `saltlen` in case we decide to later
 * internalize the preprocessing of `salt` to a string of `blocksize` bytes.
 *)
(** HKDF-Extract - See https://tools.ietf.org/html/rfc5869#section-2.2 *)
val hkdf_extract :
  a       : alg ->
  prk     : uint8_p{length prk = v (HMAC.hash_size a)} ->
  salt    : uint8_p{length salt = v (HMAC.block_size a) /\ disjoint salt prk} ->
  saltlen : uint32_t{v saltlen = length salt} ->
  ikm     : uint8_p{length ikm + v (HMAC.block_size a) < pow2 32
                    /\ disjoint ikm prk /\ disjoint ikm salt} ->
  ikmlen  : uint32_t{v ikmlen = length ikm} ->
  Stack unit
    (requires (fun h0 -> live h0 prk /\ live h0 salt /\ live h0 ikm))
    (ensures  (fun h0 r h1 -> live h1 prk /\ modifies_1 prk h0 h1))

let hkdf_extract a prk salt saltlen ikm ikmlen =
  HMAC.hmac a prk salt saltlen ikm ikmlen


(** Inner loop of HKDF-Expand *)
private val hkdf_expand_inner:
  a       : alg ->
  state   : uint8_p ->
  prk     : uint8_p {length prk = v (HMAC.block_size a) /\ disjoint prk state} ->
  prklen  : uint32_t {v prklen = length prk} ->
  info    : uint8_p ->
  infolen : uint32_t {v infolen = length info} ->
  n       : uint32_t {v n <= pow2 8} ->
  i       : uint32_t {v i <= v n} ->
  StackInline unit
    (requires (fun h0 -> live h0 state /\ live h0 prk /\ live h0 info
       /\ v (HMAC.hash_size a +^ HMAC.hash_size a +^ 1ul +^ U32.mul_mod n (HMAC.hash_size a))
         <= length state))
    (ensures  (fun h0 r h1 -> live h1 state /\ modifies_1 state h0 h1))

[@"c_inline"]
let hkdf_expand_inner a state prk prklen info infolen n i =
  let hashsize = HMAC.hash_size a in

  (* Recompute sizes and position of state components *)
  let size_Til = hashsize +^ infolen +^ 1ul in
  let pos_T    = hashsize +^ size_Til in
  let size_T   = U32.mul_mod n hashsize in

  (* Retrieve state components; state = T(i-1) | info | i-1 | T *)
  // TODO: Remove one of the three copies of T(i-1)
  let ti  = Buffer.sub state 0ul hashsize in      // T(i-1)
  let til = Buffer.sub state hashsize size_Til in // T(i-1) | info | i-1
  let t   = Buffer.sub state pos_T size_T in      // T(1) | ... | T(i-1)

  if i =^ 0ul then
    begin
    (* til <- info | 1 *)
    Buffer.blit info 0ul til hashsize infolen;
    Buffer.upd til (hashsize +^ infolen) 1uy;
    let til = Buffer.sub til hashsize (infolen +^ 1ul) in

    (* Compute the mac of to get block T(i) *)
    HMAC.hmac a ti prk prklen til (infolen +^ 1ul);

    (* Store the resulting block in T *)
    Buffer.blit ti 0ul t 0ul hashsize // pos = 0
    end
  else
    begin
    (* til <- T(i-1) | info | i *)
    Buffer.blit ti 0ul til 0ul hashsize;
    // Buffer.blit info 0ul til hashsize infolen; // Done in the first iteration
    Buffer.upd til (hashsize +^ infolen) (Int.Cast.uint32_to_uint8 (i +^ 1ul));

    (* Compute the mac of to get block T(i) *)
    HMAC.hmac a ti prk prklen til (hashsize +^ infolen +^ 1ul);

    (* Store the resulting block in T *)
    let pos = U32.mul_mod i hashsize in // pos +=hashsize
    Buffer.blit ti 0ul t pos hashsize
    end


(** HKDF-Expand - See https://tools.ietf.org/html/rfc5869#section-2.3 *)
val hkdf_expand :
  a       : alg ->
  okm     : uint8_p ->
  prk     : uint8_p {v (HMAC.hash_size a) <= length prk} ->
  prklen  : uint32_t {v prklen <= length prk} ->
  info    : uint8_p ->
  infolen : uint32_t {v infolen <= length info} ->
  len     : uint32_t {v len <= length okm
                    /\ v len <= (255 * U32.v (HMAC.hash_size a))
                    /\ (U32.v len / U32.v (HMAC.hash_size a) + 1) <= length okm} ->
  Stack unit
    (requires (fun h0 -> live h0 okm /\ live h0 prk /\ live h0 info))
    (ensures  (fun h0 r h1 -> live h1 okm /\ modifies_1 okm h0 h1))

let hkdf_expand a okm prk prklen info infolen len =
  push_frame ();
  let hashsize = HMAC.hash_size a in

  (* Compute the number of blocks necessary to compute the output *)
  // n = ceil(len / hashsize)
  let n_0 = if U32.(rem len hashsize) = 0ul then 0ul else 1ul in
  let n = U32.(div len hashsize) +^ n_0 in
  let n = U32.(div (len +^ hashsize -^ 1ul) hashsize) in

  (* Describe the shape of memory used by the inner loop *)
  let size_Til = hashsize +^ infolen +^ 1ul in
  let pos_T    = hashsize +^ size_Til in
  let size_T   = U32.mul_mod n hashsize in

  (* Allocate memory for inner expension: state =  T(i) | (T(i) | info | i) | T *)
  let state = Buffer.create 0uy (hashsize +^ size_Til +^ size_T) in

  (* Call the inner expension function *)
  let inv (h:mem) (i:nat) : Type0 = True in
  C.Loops.for 0ul n inv (fun i -> hkdf_expand_inner a state prk prklen info infolen n i);

  (* Extract T from the state *)
  let _T = Buffer.sub state pos_T size_T in

  (* Copy the desired part of T to okm *)
  Buffer.blit _T 0ul okm 0ul len;

  pop_frame()

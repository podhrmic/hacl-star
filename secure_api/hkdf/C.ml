open FStar_Buffer

let exit_success = 0
let exit_failure = 255

let string_of_literal s = s
let print_string = print_string

let print_bytes b len = Crypto_Symmetric_Bytes.print_buffer b 0 len

let htole16 n = if Sys.big_endian then failwith "Not implemented" else n
let le16toh n = if Sys.big_endian then n else failwith "Not implemented"

let htole32 n = if Sys.big_endian then failwith "Not implemented" else n
let le32toh n = if Sys.big_endian then n else failwith "Not implemented"

let htole64 n = if Sys.big_endian then failwith "Not implemented" else n
let le64toh n = if Sys.big_endian then n else failwith "Not implemented"

let htobe16 n = if Sys.big_endian then failwith "Not implemented" else n
let be16toh n = if Sys.big_endian then n else failwith "Not implemented"

let htobe32 n = if Sys.big_endian then failwith "Not implemented" else n
let be32toh n = if Sys.big_endian then n else failwith "Not implemented"

let htobe64 n = if Sys.big_endian then failwith "Not implemented" else n
let be64toh n = if Sys.big_endian then n else failwith "Not implemented"

let store32_le =
  let len = FStar_UInt32.uint_to_t (Prims.parse_int "4") in
  Crypto_Symmetric_Bytes.store_uint32 len

let store32_be =
  let len = FStar_UInt32.uint_to_t (Prims.parse_int "4") in
  Crypto_Symmetric_Bytes.store_big32 len

let store64_le =
  let len = FStar_UInt32.uint_to_t (Prims.parse_int "8") in
  Crypto_Symmetric_Bytes.store_uint64 len

let store64_be =
  let len = FStar_UInt32.uint_to_t (Prims.parse_int "8") in
  Crypto_Symmetric_Bytes.store_big64 len

let store128_le =
  let len = FStar_UInt32.uint_to_t (Prims.parse_int "16") in
  Crypto_Symmetric_Bytes.store_uint128 len

let store128_be =
  let len = FStar_UInt32.uint_to_t (Prims.parse_int "16") in
  Crypto_Symmetric_Bytes.store_big128 len

let load32_le =
 let len = FStar_UInt32.uint_to_t (Prims.parse_int "4") in
 Crypto_Symmetric_Bytes.load_uint32 len

let load32_be =
 let len = FStar_UInt32.uint_to_t (Prims.parse_int "4") in
  Crypto_Symmetric_Bytes.load_big32 len

let load64_le =
 let len = FStar_UInt32.uint_to_t (Prims.parse_int "8") in
  Crypto_Symmetric_Bytes.load_uint64 len

let load64_be =
 let len = FStar_UInt32.uint_to_t (Prims.parse_int "8") in
  Crypto_Symmetric_Bytes.load_big64 len

let load128_le =
 let len = FStar_UInt32.uint_to_t (Prims.parse_int "16") in
  Crypto_Symmetric_Bytes.load_uint128 len

let load128_be =
 let len = FStar_UInt32.uint_to_t (Prims.parse_int "16") in
  Crypto_Symmetric_Bytes.load_big128 len

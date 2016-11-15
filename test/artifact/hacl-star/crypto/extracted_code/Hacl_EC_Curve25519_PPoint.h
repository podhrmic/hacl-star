/* This file auto-generated by KreMLin! */
#ifndef __Hacl_EC_Curve25519_PPoint_H
#define __Hacl_EC_Curve25519_PPoint_H


#include "Prims.h"
#include "FStar_Mul.h"
#include "FStar_Squash.h"
#include "FStar_StrongExcludedMiddle.h"
#include "FStar_List_Tot.h"
#include "FStar_Classical.h"
#include "FStar_ListProperties.h"
#include "FStar_SeqProperties.h"
#include "FStar_Math_Lemmas.h"
#include "FStar_BitVector.h"
#include "FStar_UInt.h"
#include "FStar_Int.h"
#include "FStar_FunctionalExtensionality.h"
#include "FStar_PropositionalExtensionality.h"
#include "FStar_PredicateExtensionality.h"
#include "FStar_TSet.h"
#include "FStar_Set.h"
#include "FStar_Map.h"
#include "FStar_Ghost.h"
#include "FStar_All.h"
#include "Hacl_UInt64.h"
#include "Hacl_UInt128.h"
#include "Hacl_UInt32.h"
#include "Hacl_UInt8.h"
#include "Hacl_Cast.h"
#include "FStar_Buffer.h"
#include "FStar_Buffer_Quantifiers.h"
#include "Hacl_EC_Curve25519_Parameters.h"
#include "Hacl_EC_Curve25519_Bigint.h"
#include "Hacl_EC_Curve25519_Utils.h"
#include "Hacl_EC_Curve25519_Bignum_Fproduct.h"
#include "Hacl_EC_Curve25519_Bignum_Fscalar.h"
#include "Hacl_EC_Curve25519_Bignum_Fdifference.h"
#include "Hacl_EC_Curve25519_Bignum_Fsum.h"
#include "Hacl_EC_Curve25519_Bignum_Modulo.h"
#include "Hacl_EC_Curve25519_Bignum.h"
#include "kremlib.h"

typedef struct {
  uint64_t *x00;
  uint64_t *x01;
  uint64_t *x02;
}
Hacl_EC_Curve25519_PPoint_point;

uint64_t *Hacl_EC_Curve25519_PPoint____Point___x(Hacl_EC_Curve25519_PPoint_point projectee);

uint64_t *Hacl_EC_Curve25519_PPoint____Point___y(Hacl_EC_Curve25519_PPoint_point projectee);

uint64_t *Hacl_EC_Curve25519_PPoint____Point___z(Hacl_EC_Curve25519_PPoint_point projectee);

uint64_t *Hacl_EC_Curve25519_PPoint_get_x(Hacl_EC_Curve25519_PPoint_point p);

uint64_t *Hacl_EC_Curve25519_PPoint_get_y(Hacl_EC_Curve25519_PPoint_point p);

uint64_t *Hacl_EC_Curve25519_PPoint_get_z(Hacl_EC_Curve25519_PPoint_point p);

Hacl_EC_Curve25519_PPoint_point
Hacl_EC_Curve25519_PPoint_make(uint64_t *x, uint64_t *y, uint64_t *z);

Prims_prop
(*Hacl_EC_Curve25519_PPoint_refs(Hacl_EC_Curve25519_PPoint_point p))(FStar_Heap_aref x0);

void
Hacl_EC_Curve25519_PPoint_swap_conditional_aux_(
  uint64_t *a,
  uint64_t *b,
  uint64_t swap,
  uint32_t ctr
);

void Hacl_EC_Curve25519_PPoint_swap_conditional_aux(uint64_t *a, uint64_t *b, uint64_t swap);

FStar_HyperHeap_rid Hacl_EC_Curve25519_PPoint_frame_of(Hacl_EC_Curve25519_PPoint_point p);

void
Hacl_EC_Curve25519_PPoint_helper_lemma_2(
  FStar_HyperHeap_rid r,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  Prims_prop (*sub)(FStar_Heap_aref x0),
  Prims_prop (*s)(FStar_Heap_aref x0)
);

void
Hacl_EC_Curve25519_PPoint_helper_lemma_3(
  FStar_HyperHeap_rid r,
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  FStar_HyperStack_mem h2,
  Prims_prop (*s)(FStar_Heap_aref x0)
);

void
Hacl_EC_Curve25519_PPoint_swap_conditional(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b,
  uint64_t is_swap
);

void
Hacl_EC_Curve25519_PPoint_copy(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b
);

void
Hacl_EC_Curve25519_PPoint_swap(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b
);

void
Hacl_EC_Curve25519_PPoint_helper_lemma_5(
  FStar_HyperStack_mem h0,
  FStar_HyperStack_mem h1,
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b
);

void
Hacl_EC_Curve25519_PPoint_swap_both(
  Hacl_EC_Curve25519_PPoint_point a,
  Hacl_EC_Curve25519_PPoint_point b,
  Hacl_EC_Curve25519_PPoint_point c,
  Hacl_EC_Curve25519_PPoint_point d
);

void
Hacl_EC_Curve25519_PPoint_copy2(
  Hacl_EC_Curve25519_PPoint_point p_,
  Hacl_EC_Curve25519_PPoint_point q_,
  Hacl_EC_Curve25519_PPoint_point p,
  Hacl_EC_Curve25519_PPoint_point q
);
#endif
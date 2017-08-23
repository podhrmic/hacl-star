HACL_HOME?=../..
FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=../../../kremlin

include ../Makefile
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

KRML_ARGS=$(FPIC) -ccopt -maes \
  $(KREMLIN_HOME)/test/../kremlib/testlib.c \
  -drop Hacl.Spe.*,Spec,Hacl.Spec,Spec.*,Hacl.Spec.* \
  -add-include '"testlib.h"' -bundle "Hacl.*" $(KOPTS)

NOEXTRACT=$(FSTAR_DEFAULT_ARGS) $(addprefix --no_extract Hacl., UInt64 UInt32 UInt8)


test-spec-hmac512.exe: Spec.Test.HMAC.SHA2_512.fst
	mkdir -p tmp
	$(FSTAR) --codegen OCaml --lax $(NOEXTRACT) --odir tmp $^
	$(OCAMLOPT) -I tmp $(OCAML_INCLUDES) -package fstarlib \
	tmp/FStar_Seq.ml \
	tmp/FStar_Endianness.ml \
	tmp/Spec_Loops.ml \
	tmp/Spec_Lib.ml \
	tmp/Seq_Create.ml \
	tmp/Spec_SHA2_512.ml \
	tmp/Spec_HMAC_SHA2_512.ml \
	TestLibSeq.ml \
	tmp/$(subst .,_,$(basename $<)).ml \
	-o $@
	./$@

test-hmac.exe: Crypto.Test.HMAC.fst
	$(KRML) ../test/test_hacl/Crypto.Indexing.fst Crypto.Test.HMAC.fst \
	 -tmpdir tmp -o $@ -no-prefix Crypto.Test.HMAC
	./$@

test-hkdf.exe: Crypto.Test.HKDF.fst
	$(KRML) ../test/test_hacl/Crypto.Indexing.fst Crypto.Test.HKDF.fst \
	 -tmpdir tmp -o $@ -no-prefix Crypto.Test.HKDF
	./$@

test-hmac-ocaml.exe: Crypto.Test.HMAC.fst
	mkdir -p tmp
	$(FSTAR) --codegen OCaml --lax $(NOEXTRACT) --no_extract C --odir tmp $^
	cp C.ml tmp
	$(OCAMLOPT) -I tmp -I $(KREMLIN_HOME)/kremlib $(OCAML_INCLUDES) -package fstarlib \
	tmp/FStar_Endianness.ml \
	tmp/Crypto_Symmetric_Bytes.ml \
	tmp/C_Loops.ml \
	tmp/C.ml \
	$(KREMLIN_HOME)/kremlib/TestLib.ml \
	tmp/Hacl_UInt128.ml \
	tmp/Hacl_Endianness.ml \
	tmp/Hacl_Hash_Lib_Create.ml \
	tmp/Hacl_Hash_Lib_LoadStore.ml \
	tmp/Spec_Loops.ml \
	tmp/Spec_Lib.ml \
	tmp/Seq_Create.ml \
	tmp/Spec_SHA2_256.ml \
	tmp/Hacl_Hash_SHA2_256.ml \
	tmp/Spec_SHA2_384.ml \
	tmp/Hacl_Hash_SHA2_384.ml \
	tmp/Spec_SHA2_512.ml \
	tmp/Hacl_Hash_SHA2_512.ml \
	tmp/Crypto_HMAC.ml \
	tmp/$(subst .,_,$(basename $<)).ml \
	-o $@
	./$@

test-hkdf-ocaml.exe: Crypto.Test.HKDF.fst
	mkdir -p tmp
	$(FSTAR) --codegen OCaml --lax $(NOEXTRACT) --no_extract C --odir tmp $^
	cp C.ml tmp
	$(OCAMLOPT) -I tmp -I $(KREMLIN_HOME)/kremlib $(OCAML_INCLUDES) -package fstarlib \
	tmp/FStar_Endianness.ml \
	tmp/Crypto_Symmetric_Bytes.ml \
	tmp/C_Loops.ml \
	tmp/C.ml \
	$(KREMLIN_HOME)/kremlib/TestLib.ml \
	tmp/Hacl_UInt128.ml \
	tmp/Hacl_Endianness.ml \
	tmp/Hacl_Hash_Lib_Create.ml \
	tmp/Hacl_Hash_Lib_LoadStore.ml \
	tmp/Spec_Loops.ml \
	tmp/Spec_Lib.ml \
	tmp/Seq_Create.ml \
	tmp/Spec_SHA2_256.ml \
	tmp/Hacl_Hash_SHA2_256.ml \
	tmp/Spec_SHA2_384.ml \
	tmp/Hacl_Hash_SHA2_384.ml \
	tmp/Spec_SHA2_512.ml \
	tmp/Hacl_Hash_SHA2_512.ml \
	tmp/Crypto_HMAC.ml \
	tmp/Crypto_HKDF.ml \
	tmp/$(subst .,_,$(basename $<)).ml \
	-o $@
	./$@

CCOPTS=-Ofast -march=native -mtune=native -m64 -fwrapv -fomit-frame-pointer -funroll-loops \
-I $(KREMLIN_HOME)/kremlib -I $(HACL_HOME)/test/c -I tmp \
-Wno-bitwise-op-parentheses -Wno-shift-op-parentheses

test-hkdf-perf.exe: test-hkdf-perf.c Crypto.HKDF.fst 
	$(CC) $(CCOPTS) -o $(subst .,_,$(basename $<)).exe \
	$(HACL_HOME)/test/c/hacl_test_utils.c \
	$(KREMLIN_HOME)/kremlib/kremlib.c \
	$(KREMLIN_HOME)/kremlib/testlib.c \
	tmp/FStar.c tmp/Hacl.c tmp/Crypto_HMAC.c tmp/Crypto_HKDF.c $<
	./$@

HACL_HOME?=../..
FSTAR_HOME?=../../../FStar
KREMLIN_HOME?=../../../kremlin

include ../Makefile
include $(FSTAR_HOME)/src/gmake/z3.mk
include $(FSTAR_HOME)/src/gmake/fstar.mk
include $(FSTAR_HOME)/ulib/ml/Makefile.include

KRML_ARGS=$(FPIC) -ccopt -maes -fnouint128 \
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
	TestLib.ml \
	tmp/$(subst .,_,$(basename $<)).ml \
	-o $@
	./$@

tmp/out.krml: Crypto.Test.HMAC.fst
	$(KRML) ../test/test_hacl/Crypto.Indexing.fst Crypto.Test.HMAC.fst \
	  -tmpdir tmp -skip-translation

test-hmac.exe: tmp/out.krml
	$(KRML) $< -tmpdir tmp -o $@ -no-prefix Crypto.Test.HMAC
	./$@	

test-hmac-ocaml.exe: Crypto.Test.HMAC.fst
	mkdir -p tmp
#	$(FSTAR) --codegen OCaml --lax $(NOEXTRACT) --no_extract C --odir tmp $^
	cp C.ml tmp
	$(OCAMLOPT) -I tmp -I $(KREMLIN_HOME)/kremlib $(OCAML_INCLUDES) -package fstarlib \
	tmp/FStar_Endianness.ml \
	tmp/FStar_Seq.ml \
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

clean:
	rm -rf tmp *.exe *.dSYM


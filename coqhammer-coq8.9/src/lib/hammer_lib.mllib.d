src/lib/hammer_lib_MLLIB_DEPENDENCIES:=src/lib/hhutils src/lib/hhlib src/lib/lpo src/lib/g_hammer_lib
src/lib/hammer_lib.cma:$(addsuffix .cmo,$(src/lib/hammer_lib_MLLIB_DEPENDENCIES))
src/lib/hammer_lib.cmxa:$(addsuffix .cmx,$(src/lib/hammer_lib_MLLIB_DEPENDENCIES))

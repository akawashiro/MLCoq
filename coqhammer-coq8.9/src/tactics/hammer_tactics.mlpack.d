src/tactics/hammer_tactics_MLPACK_DEPENDENCIES:=src/tactics/sauto src/tactics/g_tactics
src/tactics/hammer_tactics.cmo:$(addsuffix .cmo,$(src/tactics/hammer_tactics_MLPACK_DEPENDENCIES))
src/tactics/hammer_tactics.cmx:$(addsuffix .cmx,$(src/tactics/hammer_tactics_MLPACK_DEPENDENCIES))
src/tactics/sauto.cmx : FOR_PACK=-for-pack Hammer_tactics
src/tactics/g_tactics.cmx : FOR_PACK=-for-pack Hammer_tactics

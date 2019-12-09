src/plugin/hammer_plugin_MLPACK_DEPENDENCIES:=src/plugin/hammer_errors src/plugin/hh_term src/plugin/msg src/plugin/timeout src/plugin/coq_transl_opts src/plugin/coqterms src/plugin/defhash src/plugin/coq_typing src/plugin/hashing src/plugin/coq_convert src/plugin/tptp_out src/plugin/coq_transl src/plugin/opt src/plugin/parallel src/plugin/features src/plugin/provers src/plugin/partac src/plugin/g_hammer
src/plugin/hammer_plugin.cmo:$(addsuffix .cmo,$(src/plugin/hammer_plugin_MLPACK_DEPENDENCIES))
src/plugin/hammer_plugin.cmx:$(addsuffix .cmx,$(src/plugin/hammer_plugin_MLPACK_DEPENDENCIES))
src/plugin/hammer_errors.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/hh_term.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/msg.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/timeout.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/coq_transl_opts.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/coqterms.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/defhash.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/coq_typing.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/hashing.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/coq_convert.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/tptp_out.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/coq_transl.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/opt.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/parallel.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/features.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/provers.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/partac.cmx : FOR_PACK=-for-pack Hammer_plugin
src/plugin/g_hammer.cmx : FOR_PACK=-for-pack Hammer_plugin

plugins/btauto/g_btauto.cmo : plugins/ltac/tacentries.cmi \
    plugins/btauto/refl_btauto.cmo vernac/mltop.cmi \
    plugins/ltac/ltac_plugin.cmo
plugins/btauto/g_btauto.cmx : plugins/ltac/tacentries.cmx \
    plugins/btauto/refl_btauto.cmx vernac/mltop.cmx \
    plugins/ltac/ltac_plugin.cmx
plugins/btauto/refl_btauto.cmo : engine/univGen.cmi engine/termops.cmi \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    engine/proofview.cmi printing/printer.cmi lib/pp.cmi proofs/pfedit.cmi \
    kernel/names.cmi clib/int.cmi library/globnames.cmi interp/genredexpr.cmo \
    engine/eConstr.cmi library/coqlib.cmi kernel/constr.cmi lib/cErrors.cmi
plugins/btauto/refl_btauto.cmx : engine/univGen.cmx engine/termops.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    engine/proofview.cmx printing/printer.cmx lib/pp.cmx proofs/pfedit.cmx \
    kernel/names.cmx clib/int.cmx library/globnames.cmx interp/genredexpr.cmx \
    engine/eConstr.cmx library/coqlib.cmx kernel/constr.cmx lib/cErrors.cmx
plugins/cc/ccalgo.cmo : kernel/vars.cmi lib/util.cmi pretyping/typing.cmi \
    kernel/term.cmi proofs/tacmach.cmi kernel/sorts.cmi printing/printer.cmi \
    lib/pp.cmi proofs/pfedit.cmi kernel/names.cmi engine/namegen.cmi \
    clib/int.cmi clib/hashset.cmi library/goptions.cmi lib/feedback.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi lib/control.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    plugins/cc/ccalgo.cmi
plugins/cc/ccalgo.cmx : kernel/vars.cmx lib/util.cmx pretyping/typing.cmx \
    kernel/term.cmx proofs/tacmach.cmx kernel/sorts.cmx printing/printer.cmx \
    lib/pp.cmx proofs/pfedit.cmx kernel/names.cmx engine/namegen.cmx \
    clib/int.cmx clib/hashset.cmx library/goptions.cmx lib/feedback.cmx \
    engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx lib/control.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    plugins/cc/ccalgo.cmi
plugins/cc/ccalgo.cmi : lib/util.cmi kernel/sorts.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi proofs/goal.cmi engine/evd.cmi \
    kernel/constr.cmi clib/cSig.cmi
plugins/cc/ccproof.cmo : lib/pp.cmi kernel/constr.cmi plugins/cc/ccalgo.cmi \
    lib/cErrors.cmi plugins/cc/ccproof.cmi
plugins/cc/ccproof.cmx : lib/pp.cmx kernel/constr.cmx plugins/cc/ccalgo.cmx \
    lib/cErrors.cmx plugins/cc/ccproof.cmi
plugins/cc/ccproof.cmi : kernel/constr.cmi plugins/cc/ccalgo.cmi
plugins/cc/cctac.cmo : kernel/vars.cmi lib/util.cmi pretyping/typing.cmi \
    kernel/type_errors.cmi engine/termops.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi pretyping/retyping.cmi \
    proofs/refine.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    printing/printer.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    kernel/names.cmi engine/namegen.cmi clib/int.cmi \
    pretyping/inductiveops.cmi library/global.cmi pretyping/glob_term.cmo \
    lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarsolve.cmi engine/evar_kinds.cmi tactics/equality.cmi \
    engine/eConstr.cmi pretyping/detyping.cmi kernel/declarations.cmo \
    lib/dAst.cmi library/coqlib.cmi kernel/context.cmi kernel/constr.cmi \
    plugins/cc/ccproof.cmi plugins/cc/ccalgo.cmi kernel/cClosure.cmi \
    plugins/cc/cctac.cmi
plugins/cc/cctac.cmx : kernel/vars.cmx lib/util.cmx pretyping/typing.cmx \
    kernel/type_errors.cmx engine/termops.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx pretyping/retyping.cmx \
    proofs/refine.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    printing/printer.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    kernel/names.cmx engine/namegen.cmx clib/int.cmx \
    pretyping/inductiveops.cmx library/global.cmx pretyping/glob_term.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarsolve.cmx engine/evar_kinds.cmx tactics/equality.cmx \
    engine/eConstr.cmx pretyping/detyping.cmx kernel/declarations.cmx \
    lib/dAst.cmx library/coqlib.cmx kernel/context.cmx kernel/constr.cmx \
    plugins/cc/ccproof.cmx plugins/cc/ccalgo.cmx kernel/cClosure.cmx \
    plugins/cc/cctac.cmi
plugins/cc/cctac.cmi : engine/proofview.cmi engine/eConstr.cmi \
    plugins/cc/ccproof.cmi
plugins/cc/g_congruence.cmo : plugins/ltac/tacentries.cmi interp/stdarg.cmi \
    vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo lib/genarg.cmi \
    parsing/extend.cmo plugins/cc/cctac.cmi
plugins/cc/g_congruence.cmx : plugins/ltac/tacentries.cmx interp/stdarg.cmx \
    vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx lib/genarg.cmx \
    parsing/extend.cmx plugins/cc/cctac.cmx
plugins/derive/derive.cmo : kernel/vars.cmi kernel/safe_typing.cmi \
    engine/proofview.cmi proofs/proof_global.cmi proofs/proof.cmi lib/pp.cmi \
    library/global.cmi lib/future.cmi engine/evd.cmi kernel/environ.cmi \
    kernel/entries.cmo engine/eConstr.cmi interp/declare.cmi \
    library/decl_kinds.cmo kernel/context.cmi interp/constrintern.cmi \
    kernel/constr.cmi lib/cErrors.cmi plugins/derive/derive.cmi
plugins/derive/derive.cmx : kernel/vars.cmx kernel/safe_typing.cmx \
    engine/proofview.cmx proofs/proof_global.cmx proofs/proof.cmx lib/pp.cmx \
    library/global.cmx lib/future.cmx engine/evd.cmx kernel/environ.cmx \
    kernel/entries.cmx engine/eConstr.cmx interp/declare.cmx \
    library/decl_kinds.cmx kernel/context.cmx interp/constrintern.cmx \
    kernel/constr.cmx lib/cErrors.cmx plugins/derive/derive.cmi
plugins/derive/derive.cmi : kernel/names.cmi interp/constrexpr.cmo
plugins/derive/g_derive.cmo : vernac/vernacexpr.cmo vernac/vernacentries.cmi \
    interp/stdarg.cmi vernac/mltop.cmi lib/genarg.cmi parsing/extend.cmo \
    plugins/derive/derive.cmi
plugins/derive/g_derive.cmx : vernac/vernacexpr.cmx vernac/vernacentries.cmx \
    interp/stdarg.cmx vernac/mltop.cmx lib/genarg.cmx parsing/extend.cmx \
    plugins/derive/derive.cmx
plugins/extraction/big.cmo :
plugins/extraction/big.cmx :
plugins/extraction/common.cmo : lib/util.cmi clib/unicode.cmi \
    plugins/extraction/table.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi plugins/extraction/mlutil.cmi \
    plugins/extraction/miniml.cmi library/libnames.cmi clib/int.cmi \
    library/globnames.cmi plugins/extraction/common.cmi
plugins/extraction/common.cmx : lib/util.cmx clib/unicode.cmx \
    plugins/extraction/table.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx plugins/extraction/mlutil.cmx \
    plugins/extraction/miniml.cmx library/libnames.cmx clib/int.cmx \
    library/globnames.cmx plugins/extraction/common.cmi
plugins/extraction/common.cmi : lib/pp.cmi kernel/names.cmi \
    plugins/extraction/miniml.cmi
plugins/extraction/extract_env.cmo : vernac/vernacentries.cmi lib/util.cmi \
    vernac/topfmt.cmi plugins/extraction/table.cmi interp/smartlocate.cmi \
    plugins/extraction/scheme.cmi kernel/reduction.cmi \
    proofs/proof_global.cmi proofs/proof.cmi lib/pp.cmi proofs/pfedit.cmi \
    clib/option.cmi plugins/extraction/ocaml.cmi library/nametab.cmi \
    kernel/names.cmi plugins/extraction/modutil.cmi kernel/modops.cmi \
    kernel/mod_typing.cmi kernel/mod_subst.cmi plugins/extraction/mlutil.cmi \
    plugins/extraction/miniml.cmi library/library.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi plugins/extraction/json.cmi \
    clib/int.cmi plugins/extraction/haskell.cmi library/globnames.cmi \
    library/global.cmi lib/flags.cmi lib/feedback.cmi \
    plugins/extraction/extraction.cmi engine/evd.cmi lib/envars.cmi \
    engine/eConstr.cmi kernel/declarations.cmo interp/constrexpr.cmo \
    kernel/constr.cmi plugins/extraction/common.cmi clib/cUnix.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/extraction/extract_env.cmi
plugins/extraction/extract_env.cmx : vernac/vernacentries.cmx lib/util.cmx \
    vernac/topfmt.cmx plugins/extraction/table.cmx interp/smartlocate.cmx \
    plugins/extraction/scheme.cmx kernel/reduction.cmx \
    proofs/proof_global.cmx proofs/proof.cmx lib/pp.cmx proofs/pfedit.cmx \
    clib/option.cmx plugins/extraction/ocaml.cmx library/nametab.cmx \
    kernel/names.cmx plugins/extraction/modutil.cmx kernel/modops.cmx \
    kernel/mod_typing.cmx kernel/mod_subst.cmx plugins/extraction/mlutil.cmx \
    plugins/extraction/miniml.cmx library/library.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx plugins/extraction/json.cmx \
    clib/int.cmx plugins/extraction/haskell.cmx library/globnames.cmx \
    library/global.cmx lib/flags.cmx lib/feedback.cmx \
    plugins/extraction/extraction.cmx engine/evd.cmx lib/envars.cmx \
    engine/eConstr.cmx kernel/declarations.cmx interp/constrexpr.cmx \
    kernel/constr.cmx plugins/extraction/common.cmx clib/cUnix.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/extraction/extract_env.cmi
plugins/extraction/extract_env.cmi : lib/pp.cmi kernel/names.cmi \
    plugins/extraction/miniml.cmi library/libnames.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi
plugins/extraction/extraction.cmo : lib/util.cmi engine/univGen.cmi \
    clib/unicode.cmi engine/termops.cmi kernel/term.cmi \
    plugins/extraction/table.cmi kernel/sorts.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi pretyping/recordops.cmi \
    clib/option.cmi kernel/opaqueproof.cmi kernel/names.cmi \
    engine/namegen.cmi kernel/mod_subst.cmi plugins/extraction/mlutil.cmi \
    plugins/extraction/miniml.cmi clib/int.cmi pretyping/inductiveops.cmi \
    kernel/inductive.cmi lib/hook.cmi library/globnames.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/declareops.cmi \
    kernel/declarations.cmo kernel/context.cmi kernel/constr.cmi \
    lib/cErrors.cmi plugins/extraction/extraction.cmi
plugins/extraction/extraction.cmx : lib/util.cmx engine/univGen.cmx \
    clib/unicode.cmx engine/termops.cmx kernel/term.cmx \
    plugins/extraction/table.cmx kernel/sorts.cmx pretyping/retyping.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx pretyping/recordops.cmx \
    clib/option.cmx kernel/opaqueproof.cmx kernel/names.cmx \
    engine/namegen.cmx kernel/mod_subst.cmx plugins/extraction/mlutil.cmx \
    plugins/extraction/miniml.cmx clib/int.cmx pretyping/inductiveops.cmx \
    kernel/inductive.cmx lib/hook.cmx library/globnames.cmx engine/evd.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/declareops.cmx \
    kernel/declarations.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cErrors.cmx plugins/extraction/extraction.cmi
plugins/extraction/extraction.cmi : kernel/names.cmi \
    plugins/extraction/miniml.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/declarations.cmo kernel/constr.cmi
plugins/extraction/g_extraction.cmo : vernac/vernacentries.cmi \
    stm/vernac_classifier.cmi plugins/ltac/tacsubst.cmi \
    plugins/ltac/tacinterp.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacentries.cmi \
    plugins/extraction/table.cmi interp/stdarg.cmi plugins/ltac/pptactic.cmi \
    lib/pp.cmi parsing/pcoq.cmi kernel/names.cmi vernac/mltop.cmi \
    plugins/ltac/ltac_plugin.cmo pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi engine/ftactic.cmi lib/feedback.cmi \
    plugins/extraction/extract_env.cmi parsing/extend.cmo lib/cWarnings.cmi \
    parsing/cLexer.cmi
plugins/extraction/g_extraction.cmx : vernac/vernacentries.cmx \
    stm/vernac_classifier.cmx plugins/ltac/tacsubst.cmx \
    plugins/ltac/tacinterp.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacentries.cmx \
    plugins/extraction/table.cmx interp/stdarg.cmx plugins/ltac/pptactic.cmx \
    lib/pp.cmx parsing/pcoq.cmx kernel/names.cmx vernac/mltop.cmx \
    plugins/ltac/ltac_plugin.cmx pretyping/geninterp.cmx interp/genintern.cmx \
    lib/genarg.cmx engine/ftactic.cmx lib/feedback.cmx \
    plugins/extraction/extract_env.cmx parsing/extend.cmx lib/cWarnings.cmx \
    parsing/cLexer.cmx
plugins/extraction/haskell.cmo : lib/util.cmi plugins/extraction/table.cmi \
    lib/pp.cmi kernel/names.cmi plugins/extraction/mlutil.cmi \
    plugins/extraction/miniml.cmi clib/int.cmi library/globnames.cmi \
    plugins/extraction/common.cmi lib/cErrors.cmi \
    plugins/extraction/haskell.cmi
plugins/extraction/haskell.cmx : lib/util.cmx plugins/extraction/table.cmx \
    lib/pp.cmx kernel/names.cmx plugins/extraction/mlutil.cmx \
    plugins/extraction/miniml.cmx clib/int.cmx library/globnames.cmx \
    plugins/extraction/common.cmx lib/cErrors.cmx \
    plugins/extraction/haskell.cmi
plugins/extraction/haskell.cmi : plugins/extraction/miniml.cmi
plugins/extraction/json.cmo : lib/util.cmi plugins/extraction/table.cmi \
    lib/pp.cmi kernel/names.cmi plugins/extraction/mlutil.cmi \
    plugins/extraction/miniml.cmi library/globnames.cmi \
    plugins/extraction/common.cmi plugins/extraction/json.cmi
plugins/extraction/json.cmx : lib/util.cmx plugins/extraction/table.cmx \
    lib/pp.cmx kernel/names.cmx plugins/extraction/mlutil.cmx \
    plugins/extraction/miniml.cmx library/globnames.cmx \
    plugins/extraction/common.cmx plugins/extraction/json.cmi
plugins/extraction/json.cmi : plugins/extraction/miniml.cmi
plugins/extraction/miniml.cmo : lib/pp.cmi kernel/names.cmi \
    plugins/extraction/miniml.cmi
plugins/extraction/miniml.cmx : lib/pp.cmx kernel/names.cmx \
    plugins/extraction/miniml.cmi
plugins/extraction/miniml.cmi : lib/pp.cmi kernel/names.cmi
plugins/extraction/mlutil.cmo : lib/util.cmi plugins/extraction/table.cmi \
    clib/option.cmi kernel/names.cmi plugins/extraction/miniml.cmi \
    library/libnames.cmi clib/int.cmi library/globnames.cmi \
    library/global.cmi kernel/declareops.cmi plugins/extraction/mlutil.cmi
plugins/extraction/mlutil.cmx : lib/util.cmx plugins/extraction/table.cmx \
    clib/option.cmx kernel/names.cmx plugins/extraction/miniml.cmx \
    library/libnames.cmx clib/int.cmx library/globnames.cmx \
    library/global.cmx kernel/declareops.cmx plugins/extraction/mlutil.cmi
plugins/extraction/mlutil.cmi : plugins/extraction/table.cmi \
    kernel/names.cmi plugins/extraction/miniml.cmi
plugins/extraction/modutil.cmo : lib/util.cmi plugins/extraction/table.cmi \
    lib/pp.cmi clib/option.cmi kernel/names.cmi plugins/extraction/mlutil.cmi \
    plugins/extraction/miniml.cmi library/globnames.cmi lib/cErrors.cmi \
    plugins/extraction/modutil.cmi
plugins/extraction/modutil.cmx : lib/util.cmx plugins/extraction/table.cmx \
    lib/pp.cmx clib/option.cmx kernel/names.cmx plugins/extraction/mlutil.cmx \
    plugins/extraction/miniml.cmx library/globnames.cmx lib/cErrors.cmx \
    plugins/extraction/modutil.cmi
plugins/extraction/modutil.cmi : kernel/names.cmi \
    plugins/extraction/miniml.cmi
plugins/extraction/ocaml.cmo : lib/util.cmi plugins/extraction/table.cmi \
    lib/pp.cmi kernel/names.cmi plugins/extraction/modutil.cmi \
    plugins/extraction/mlutil.cmi plugins/extraction/miniml.cmi clib/int.cmi \
    library/globnames.cmi plugins/extraction/common.cmi lib/cErrors.cmi \
    plugins/extraction/ocaml.cmi
plugins/extraction/ocaml.cmx : lib/util.cmx plugins/extraction/table.cmx \
    lib/pp.cmx kernel/names.cmx plugins/extraction/modutil.cmx \
    plugins/extraction/mlutil.cmx plugins/extraction/miniml.cmx clib/int.cmx \
    library/globnames.cmx plugins/extraction/common.cmx lib/cErrors.cmx \
    plugins/extraction/ocaml.cmi
plugins/extraction/ocaml.cmi : plugins/extraction/miniml.cmi
plugins/extraction/scheme.cmo : lib/util.cmi plugins/extraction/table.cmi \
    lib/pp.cmi kernel/names.cmi plugins/extraction/mlutil.cmi \
    plugins/extraction/miniml.cmi plugins/extraction/common.cmi \
    lib/cErrors.cmi plugins/extraction/scheme.cmi
plugins/extraction/scheme.cmx : lib/util.cmx plugins/extraction/table.cmx \
    lib/pp.cmx kernel/names.cmx plugins/extraction/mlutil.cmx \
    plugins/extraction/miniml.cmx plugins/extraction/common.cmx \
    lib/cErrors.cmx plugins/extraction/scheme.cmi
plugins/extraction/scheme.cmi : plugins/extraction/miniml.cmi
plugins/extraction/table.cmo : lib/util.cmi kernel/term.cmi \
    library/summary.cmi interp/smartlocate.cmi kernel/reduction.cmi \
    printing/printer.cmi lib/pp.cmi clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    plugins/extraction/miniml.cmi library/library.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi clib/int.cmi lib/hook.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    lib/flags.cmi lib/feedback.cmi kernel/environ.cmi interp/dumpglob.cmi \
    kernel/declarations.cmo lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    plugins/extraction/table.cmi
plugins/extraction/table.cmx : lib/util.cmx kernel/term.cmx \
    library/summary.cmx interp/smartlocate.cmx kernel/reduction.cmx \
    printing/printer.cmx lib/pp.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    plugins/extraction/miniml.cmx library/library.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx lib/hook.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    lib/flags.cmx lib/feedback.cmx kernel/environ.cmx interp/dumpglob.cmx \
    kernel/declarations.cmx lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    plugins/extraction/table.cmi
plugins/extraction/table.cmi : lib/pp.cmi kernel/names.cmi \
    plugins/extraction/miniml.cmi lib/loc.cmi library/libnames.cmi \
    clib/int.cmi lib/hook.cmi kernel/environ.cmi kernel/declarations.cmo \
    kernel/constr.cmi clib/cSig.cmi
plugins/firstorder/formula.cmo : kernel/vars.cmi lib/util.cmi \
    engine/termops.cmi pretyping/reductionops.cmi kernel/names.cmi \
    clib/int.cmi pretyping/inductiveops.cmi tactics/hipattern.cmi \
    library/globnames.cmi library/global.cmi engine/eConstr.cmi \
    kernel/declarations.cmo kernel/context.cmi kernel/constr.cmi \
    kernel/cClosure.cmi plugins/firstorder/formula.cmi
plugins/firstorder/formula.cmx : kernel/vars.cmx lib/util.cmx \
    engine/termops.cmx pretyping/reductionops.cmx kernel/names.cmx \
    clib/int.cmx pretyping/inductiveops.cmx tactics/hipattern.cmx \
    library/globnames.cmx library/global.cmx engine/eConstr.cmx \
    kernel/declarations.cmx kernel/context.cmx kernel/constr.cmx \
    kernel/cClosure.cmx plugins/firstorder/formula.cmi
plugins/firstorder/formula.cmi : kernel/names.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi \
    kernel/cClosure.cmi
plugins/firstorder/g_ground.cmo : vernac/vernacinterp.cmi \
    vernac/vernacentries.cmi stm/vernac_classifier.cmi tactics/tacticals.cmi \
    plugins/ltac/tactic_option.cmi plugins/ltac/tacsubst.cmi \
    proofs/tacmach.cmi plugins/ltac/tacinterp.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi \
    plugins/ltac/tacentries.cmi plugins/ltac/tacarg.cmi interp/stdarg.cmi \
    plugins/firstorder/sequent.cmi engine/proofview.cmi printing/printer.cmi \
    plugins/ltac/pptactic.cmi printing/ppconstr.cmi lib/pp.cmi \
    parsing/pcoq.cmi clib/option.cmi vernac/mltop.cmi \
    plugins/ltac/ltac_plugin.cmo vernac/locality.cmi lib/loc.cmi \
    plugins/firstorder/ground.cmi library/goptions.cmi \
    pretyping/geninterp.cmi interp/genintern.cmi lib/genarg.cmi \
    plugins/firstorder/formula.cmi lib/feedback.cmi parsing/extend.cmo \
    lib/cWarnings.cmi parsing/cLexer.cmi tactics/auto.cmi
plugins/firstorder/g_ground.cmx : vernac/vernacinterp.cmx \
    vernac/vernacentries.cmx stm/vernac_classifier.cmx tactics/tacticals.cmx \
    plugins/ltac/tactic_option.cmx plugins/ltac/tacsubst.cmx \
    proofs/tacmach.cmx plugins/ltac/tacinterp.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx \
    plugins/ltac/tacentries.cmx plugins/ltac/tacarg.cmx interp/stdarg.cmx \
    plugins/firstorder/sequent.cmx engine/proofview.cmx printing/printer.cmx \
    plugins/ltac/pptactic.cmx printing/ppconstr.cmx lib/pp.cmx \
    parsing/pcoq.cmx clib/option.cmx vernac/mltop.cmx \
    plugins/ltac/ltac_plugin.cmx vernac/locality.cmx lib/loc.cmx \
    plugins/firstorder/ground.cmx library/goptions.cmx \
    pretyping/geninterp.cmx interp/genintern.cmx lib/genarg.cmx \
    plugins/firstorder/formula.cmx lib/feedback.cmx parsing/extend.cmx \
    lib/cWarnings.cmx parsing/cLexer.cmx tactics/auto.cmx
plugins/firstorder/ground.cmo : tactics/tacticals.cmi \
    plugins/ltac/tactic_debug.cmi proofs/tacmach.cmi \
    plugins/ltac/tacinterp.cmi plugins/firstorder/sequent.cmi \
    plugins/firstorder/rules.cmi engine/proofview.cmi printing/printer.cmi \
    lib/pp.cmi kernel/names.cmi plugins/ltac/ltac_plugin.cmo \
    plugins/firstorder/instances.cmi clib/heap.cmi library/globnames.cmi \
    plugins/firstorder/formula.cmi lib/feedback.cmi engine/evd.cmi \
    pretyping/classops.cmi kernel/cClosure.cmi plugins/firstorder/ground.cmi
plugins/firstorder/ground.cmx : tactics/tacticals.cmx \
    plugins/ltac/tactic_debug.cmx proofs/tacmach.cmx \
    plugins/ltac/tacinterp.cmx plugins/firstorder/sequent.cmx \
    plugins/firstorder/rules.cmx engine/proofview.cmx printing/printer.cmx \
    lib/pp.cmx kernel/names.cmx plugins/ltac/ltac_plugin.cmx \
    plugins/firstorder/instances.cmx clib/heap.cmx library/globnames.cmx \
    plugins/firstorder/formula.cmx lib/feedback.cmx engine/evd.cmx \
    pretyping/classops.cmx kernel/cClosure.cmx plugins/firstorder/ground.cmi
plugins/firstorder/ground.cmi : plugins/firstorder/sequent.cmi \
    engine/proofview.cmi
plugins/firstorder/instances.cmo : kernel/vars.cmi lib/util.cmi \
    plugins/firstorder/unify.cmi pretyping/typing.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    plugins/firstorder/sequent.cmi plugins/firstorder/rules.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi clib/heap.cmi library/globnames.cmi \
    plugins/firstorder/formula.cmi engine/evd.cmi engine/evarutil.cmi \
    engine/eConstr.cmi kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    plugins/firstorder/instances.cmi
plugins/firstorder/instances.cmx : kernel/vars.cmx lib/util.cmx \
    plugins/firstorder/unify.cmx pretyping/typing.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    plugins/firstorder/sequent.cmx plugins/firstorder/rules.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx lib/pp.cmx \
    kernel/names.cmx clib/int.cmx clib/heap.cmx library/globnames.cmx \
    plugins/firstorder/formula.cmx engine/evd.cmx engine/evarutil.cmx \
    engine/eConstr.cmx kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    plugins/firstorder/instances.cmi
plugins/firstorder/instances.cmi : plugins/firstorder/unify.cmi \
    plugins/firstorder/sequent.cmi plugins/firstorder/rules.cmi \
    kernel/names.cmi plugins/firstorder/formula.cmi engine/evd.cmi
plugins/firstorder/rules.cmo : kernel/vars.cmi lib/util.cmi \
    engine/univGen.cmi engine/termops.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi plugins/firstorder/sequent.cmi \
    engine/proofview.cmi lib/pp.cmi kernel/names.cmi pretyping/locus.cmo \
    library/globnames.cmi plugins/firstorder/formula.cmi engine/eConstr.cmi \
    library/coqlib.cmi lib/control.cmi kernel/context.cmi kernel/constr.cmi \
    lib/cErrors.cmi plugins/firstorder/rules.cmi
plugins/firstorder/rules.cmx : kernel/vars.cmx lib/util.cmx \
    engine/univGen.cmx engine/termops.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx plugins/firstorder/sequent.cmx \
    engine/proofview.cmx lib/pp.cmx kernel/names.cmx pretyping/locus.cmx \
    library/globnames.cmx plugins/firstorder/formula.cmx engine/eConstr.cmx \
    library/coqlib.cmx lib/control.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cErrors.cmx plugins/firstorder/rules.cmi
plugins/firstorder/rules.cmi : plugins/firstorder/sequent.cmi \
    engine/proofview.cmi kernel/names.cmi engine/eConstr.cmi \
    kernel/constr.cmi
plugins/firstorder/sequent.cmo : lib/util.cmi plugins/firstorder/unify.cmi \
    pretyping/typing.cmi engine/termops.cmi printing/printer.cmi \
    printing/ppconstr.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    clib/int.cmi pretyping/inductiveops.cmi tactics/hints.cmi clib/heap.cmi \
    library/globnames.cmi library/global.cmi plugins/firstorder/formula.cmi \
    engine/evd.cmi engine/eConstr.cmi interp/constrextern.cmi \
    kernel/constr.cmi lib/cErrors.cmi plugins/firstorder/sequent.cmi
plugins/firstorder/sequent.cmx : lib/util.cmx plugins/firstorder/unify.cmx \
    pretyping/typing.cmx engine/termops.cmx printing/printer.cmx \
    printing/ppconstr.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    clib/int.cmx pretyping/inductiveops.cmx tactics/hints.cmx clib/heap.cmx \
    library/globnames.cmx library/global.cmx plugins/firstorder/formula.cmx \
    engine/evd.cmx engine/eConstr.cmx interp/constrextern.cmx \
    kernel/constr.cmx lib/cErrors.cmx plugins/firstorder/sequent.cmi
plugins/firstorder/sequent.cmi : lib/pp.cmi kernel/names.cmi \
    tactics/hints.cmi clib/heap.cmi plugins/firstorder/formula.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi \
    clib/cSig.cmi
plugins/firstorder/unify.cmo : kernel/vars.cmi lib/util.cmi \
    engine/termops.cmi pretyping/reductionops.cmi clib/int.cmi \
    engine/eConstr.cmi kernel/constr.cmi plugins/firstorder/unify.cmi
plugins/firstorder/unify.cmx : kernel/vars.cmx lib/util.cmx \
    engine/termops.cmx pretyping/reductionops.cmx clib/int.cmx \
    engine/eConstr.cmx kernel/constr.cmx plugins/firstorder/unify.cmi
plugins/firstorder/unify.cmi : engine/evd.cmi engine/eConstr.cmi \
    kernel/constr.cmi
plugins/funind/functional_principles_proofs.cmo : vernac/vernacexpr.cmo \
    kernel/vars.cmi lib/util.cmi engine/univGen.cmi pretyping/typing.cmi \
    engine/termops.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    pretyping/tacred.cmi proofs/tacmach.cmi proofs/refiner.cmi \
    pretyping/reductionops.cmi interp/redops.cmi plugins/funind/recdef.cmi \
    engine/proofview.cmi proofs/proof_global.cmi printing/printer.cmi \
    printing/ppconstr.cmi lib/pp.cmi proofs/pfedit.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi pretyping/locusops.cmi pretyping/locus.cmo \
    library/libnames.cmi vernac/lemmas.cmi clib/int.cmi \
    plugins/funind/indfun_common.cmi tactics/hints.cmi library/globnames.cmi \
    library/global.cmi interp/genredexpr.cmo lib/flags.cmi lib/feedback.cmi \
    vernac/explainErr.cmi engine/evd.cmi pretyping/evarconv.cmi \
    tactics/equality.cmi kernel/environ.cmi tactics/elim.cmi \
    tactics/eauto.cmi engine/eConstr.cmi library/decl_kinds.cmo \
    library/coqlib.cmi kernel/context.cmi interp/constrintern.cmi \
    kernel/constr.cmi lib/cErrors.cmi kernel/cClosure.cmi \
    plugins/funind/functional_principles_proofs.cmi
plugins/funind/functional_principles_proofs.cmx : vernac/vernacexpr.cmx \
    kernel/vars.cmx lib/util.cmx engine/univGen.cmx pretyping/typing.cmx \
    engine/termops.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    pretyping/tacred.cmx proofs/tacmach.cmx proofs/refiner.cmx \
    pretyping/reductionops.cmx interp/redops.cmx plugins/funind/recdef.cmx \
    engine/proofview.cmx proofs/proof_global.cmx printing/printer.cmx \
    printing/ppconstr.cmx lib/pp.cmx proofs/pfedit.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx pretyping/locusops.cmx pretyping/locus.cmx \
    library/libnames.cmx vernac/lemmas.cmx clib/int.cmx \
    plugins/funind/indfun_common.cmx tactics/hints.cmx library/globnames.cmx \
    library/global.cmx interp/genredexpr.cmx lib/flags.cmx lib/feedback.cmx \
    vernac/explainErr.cmx engine/evd.cmx pretyping/evarconv.cmx \
    tactics/equality.cmx kernel/environ.cmx tactics/elim.cmx \
    tactics/eauto.cmx engine/eConstr.cmx library/decl_kinds.cmx \
    library/coqlib.cmx kernel/context.cmx interp/constrintern.cmx \
    kernel/constr.cmx lib/cErrors.cmx kernel/cClosure.cmx \
    plugins/funind/functional_principles_proofs.cmi
plugins/funind/functional_principles_proofs.cmi : proofs/tacmach.cmi \
    kernel/names.cmi plugins/funind/indfun_common.cmi engine/evd.cmi \
    engine/eConstr.cmi
plugins/funind/functional_principles_types.cmo : kernel/vars.cmi \
    lib/util.cmi engine/univGen.cmi kernel/univ.cmi pretyping/typing.cmi \
    engine/termops.cmi kernel/term.cmi tactics/tactics.cmi \
    pretyping/tacred.cmi kernel/sorts.cmi interp/smartlocate.cmi \
    kernel/safe_typing.cmi engine/proofview.cmi proofs/proof_global.cmi \
    printing/printer.cmi lib/pp.cmi proofs/pfedit.cmi clib/option.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    library/libnames.cmi vernac/lemmas.cmi clib/int.cmi pretyping/indrec.cmi \
    plugins/funind/indfun_common.cmi library/globnames.cmi library/global.cmi \
    lib/future.cmi plugins/funind/functional_principles_proofs.cmi \
    lib/flags.cmi lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    kernel/declareops.cmi interp/declare.cmi library/decl_kinds.cmo \
    kernel/context.cmi interp/constrintern.cmi kernel/constr.cmi \
    lib/cErrors.cmi clib/cEphemeron.cmi kernel/cClosure.cmi \
    plugins/funind/functional_principles_types.cmi
plugins/funind/functional_principles_types.cmx : kernel/vars.cmx \
    lib/util.cmx engine/univGen.cmx kernel/univ.cmx pretyping/typing.cmx \
    engine/termops.cmx kernel/term.cmx tactics/tactics.cmx \
    pretyping/tacred.cmx kernel/sorts.cmx interp/smartlocate.cmx \
    kernel/safe_typing.cmx engine/proofview.cmx proofs/proof_global.cmx \
    printing/printer.cmx lib/pp.cmx proofs/pfedit.cmx clib/option.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    library/libnames.cmx vernac/lemmas.cmx clib/int.cmx pretyping/indrec.cmx \
    plugins/funind/indfun_common.cmx library/globnames.cmx library/global.cmx \
    lib/future.cmx plugins/funind/functional_principles_proofs.cmx \
    lib/flags.cmx lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    kernel/declareops.cmx interp/declare.cmx library/decl_kinds.cmx \
    kernel/context.cmx interp/constrintern.cmx kernel/constr.cmx \
    lib/cErrors.cmx clib/cEphemeron.cmx kernel/cClosure.cmx \
    plugins/funind/functional_principles_types.cmi
plugins/funind/functional_principles_types.cmi : proofs/tacmach.cmi \
    kernel/sorts.cmi kernel/safe_typing.cmi kernel/names.cmi \
    library/libnames.cmi engine/evd.cmi kernel/entries.cmo engine/eConstr.cmi \
    kernel/constr.cmi
plugins/funind/g_indfun.cmo : vernac/vernacexpr.cmo vernac/vernacentries.cmi \
    stm/vernac_classifier.cmi lib/util.cmi engine/termops.cmi \
    proofs/tactypes.cmo plugins/ltac/tacsubst.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacentries.cmi plugins/ltac/tacarg.cmi interp/stdarg.cmi \
    interp/smartlocate.cmi vernac/pvernac.cmi engine/proofview.cmi \
    vernac/ppvernac.cmi plugins/ltac/pptactic.cmi lib/pp.cmi \
    plugins/ltac/pltac.cmi parsing/pcoq.cmi clib/option.cmi kernel/names.cmi \
    vernac/mltop.cmi proofs/miscprint.cmi plugins/ltac/ltac_plugin.cmo \
    lib/loc.cmi library/libnames.cmi plugins/funind/invfun.cmi \
    plugins/funind/indfun_common.cmi plugins/funind/indfun.cmi \
    library/global.cmi pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi plugins/funind/functional_principles_types.cmi \
    plugins/ltac/extratactics.cmi parsing/extend.cmo vernac/explainErr.cmi \
    clib/exninfo.cmi engine/evd.cmi engine/eConstr.cmi library/decl_kinds.cmo \
    interp/constrexpr.cmo parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi
plugins/funind/g_indfun.cmx : vernac/vernacexpr.cmx vernac/vernacentries.cmx \
    stm/vernac_classifier.cmx lib/util.cmx engine/termops.cmx \
    proofs/tactypes.cmx plugins/ltac/tacsubst.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacentries.cmx plugins/ltac/tacarg.cmx interp/stdarg.cmx \
    interp/smartlocate.cmx vernac/pvernac.cmx engine/proofview.cmx \
    vernac/ppvernac.cmx plugins/ltac/pptactic.cmx lib/pp.cmx \
    plugins/ltac/pltac.cmx parsing/pcoq.cmx clib/option.cmx kernel/names.cmx \
    vernac/mltop.cmx proofs/miscprint.cmx plugins/ltac/ltac_plugin.cmx \
    lib/loc.cmx library/libnames.cmx plugins/funind/invfun.cmx \
    plugins/funind/indfun_common.cmx plugins/funind/indfun.cmx \
    library/global.cmx pretyping/geninterp.cmx interp/genintern.cmx \
    lib/genarg.cmx plugins/funind/functional_principles_types.cmx \
    plugins/ltac/extratactics.cmx parsing/extend.cmx vernac/explainErr.cmx \
    clib/exninfo.cmx engine/evd.cmx engine/eConstr.cmx library/decl_kinds.cmx \
    interp/constrexpr.cmx parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx
plugins/funind/glob_term_to_relation.cmo : vernac/vernacexpr.cmo \
    kernel/vars.cmi lib/util.cmi pretyping/typing.cmi lib/system.cmi \
    printing/printer.cmi pretyping/pretyping.cmi vernac/ppvernac.cmi \
    printing/ppconstr.cmi lib/pp.cmi proofs/pfedit.cmi clib/option.cmi \
    kernel/names.cmi engine/namegen.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi \
    plugins/funind/indfun_common.cmi interp/impargs.cmi library/globnames.cmi \
    library/global.cmi plugins/funind/glob_termops.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    pretyping/detyping.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    lib/dAst.cmi library/coqlib.cmi kernel/context.cmi \
    interp/constrintern.cmi interp/constrextern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo kernel/constr.cmi vernac/comInductive.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/funind/glob_term_to_relation.cmi
plugins/funind/glob_term_to_relation.cmx : vernac/vernacexpr.cmx \
    kernel/vars.cmx lib/util.cmx pretyping/typing.cmx lib/system.cmx \
    printing/printer.cmx pretyping/pretyping.cmx vernac/ppvernac.cmx \
    printing/ppconstr.cmx lib/pp.cmx proofs/pfedit.cmx clib/option.cmx \
    kernel/names.cmx engine/namegen.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx \
    plugins/funind/indfun_common.cmx interp/impargs.cmx library/globnames.cmx \
    library/global.cmx plugins/funind/glob_termops.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    pretyping/detyping.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    lib/dAst.cmx library/coqlib.cmx kernel/context.cmx \
    interp/constrintern.cmx interp/constrextern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx kernel/constr.cmx vernac/comInductive.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/funind/glob_term_to_relation.cmi
plugins/funind/glob_term_to_relation.cmi : kernel/names.cmi \
    pretyping/glob_term.cmo engine/evd.cmi interp/constrexpr.cmo \
    kernel/constr.cmi
plugins/funind/glob_termops.cmo : lib/util.cmi pretyping/pretyping.cmi \
    lib/pp.cmi clib/option.cmi kernel/names.cmi engine/namegen.cmi \
    pretyping/inductiveops.cmi plugins/funind/indfun_common.cmi \
    library/globnames.cmi library/global.cmi pretyping/glob_term.cmo \
    pretyping/glob_ops.cmi engine/evd.cmi engine/evarutil.cmi \
    engine/evar_kinds.cmi engine/eConstr.cmi pretyping/detyping.cmi \
    library/decl_kinds.cmo lib/dAst.cmi library/coqlib.cmi kernel/constr.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/funind/glob_termops.cmi
plugins/funind/glob_termops.cmx : lib/util.cmx pretyping/pretyping.cmx \
    lib/pp.cmx clib/option.cmx kernel/names.cmx engine/namegen.cmx \
    pretyping/inductiveops.cmx plugins/funind/indfun_common.cmx \
    library/globnames.cmx library/global.cmx pretyping/glob_term.cmx \
    pretyping/glob_ops.cmx engine/evd.cmx engine/evarutil.cmx \
    engine/evar_kinds.cmx engine/eConstr.cmx pretyping/detyping.cmx \
    library/decl_kinds.cmx lib/dAst.cmx library/coqlib.cmx kernel/constr.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/funind/glob_termops.cmi
plugins/funind/glob_termops.cmi : pretyping/pretyping.cmi kernel/names.cmi \
    pretyping/glob_term.cmo engine/evd.cmi kernel/environ.cmi
plugins/funind/indfun.cmo : vernac/vernacexpr.cmo lib/util.cmi \
    kernel/univ.cmi pretyping/typing.cmi engine/termops.cmi \
    proofs/tactypes.cmo tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi library/states.cmi kernel/sorts.cmi interp/redops.cmi \
    plugins/funind/recdef.cmi engine/proofview.cmi printing/printer.cmi \
    pretyping/pretyping.cmi printing/ppconstr.cmi lib/pp.cmi \
    proofs/pfedit.cmi clib/option.cmi kernel/names.cmi engine/nameops.cmi \
    pretyping/locusops.cmi library/libnames.cmi vernac/lemmas.cmi \
    plugins/funind/invfun.cmi clib/int.cmi pretyping/indrec.cmi \
    plugins/funind/indfun_common.cmi library/globnames.cmi library/global.cmi \
    plugins/funind/glob_term_to_relation.cmi pretyping/glob_term.cmo \
    pretyping/glob_ops.cmi interp/genredexpr.cmo \
    plugins/funind/functional_principles_types.cmi \
    plugins/funind/functional_principles_proofs.cmi lib/flags.cmi \
    vernac/explainErr.cmi clib/exninfo.cmi engine/evd.cmi \
    tactics/equality.cmi engine/eConstr.cmi kernel/declarations.cmo \
    library/decl_kinds.cmo lib/dAst.cmi kernel/context.cmi \
    interp/constrintern.cmi interp/constrextern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo kernel/constr.cmi vernac/comFixpoint.cmi \
    vernac/comDefinition.cmi lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    plugins/funind/indfun.cmi
plugins/funind/indfun.cmx : vernac/vernacexpr.cmx lib/util.cmx \
    kernel/univ.cmx pretyping/typing.cmx engine/termops.cmx \
    proofs/tactypes.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx library/states.cmx kernel/sorts.cmx interp/redops.cmx \
    plugins/funind/recdef.cmx engine/proofview.cmx printing/printer.cmx \
    pretyping/pretyping.cmx printing/ppconstr.cmx lib/pp.cmx \
    proofs/pfedit.cmx clib/option.cmx kernel/names.cmx engine/nameops.cmx \
    pretyping/locusops.cmx library/libnames.cmx vernac/lemmas.cmx \
    plugins/funind/invfun.cmx clib/int.cmx pretyping/indrec.cmx \
    plugins/funind/indfun_common.cmx library/globnames.cmx library/global.cmx \
    plugins/funind/glob_term_to_relation.cmx pretyping/glob_term.cmx \
    pretyping/glob_ops.cmx interp/genredexpr.cmx \
    plugins/funind/functional_principles_types.cmx \
    plugins/funind/functional_principles_proofs.cmx lib/flags.cmx \
    vernac/explainErr.cmx clib/exninfo.cmx engine/evd.cmx \
    tactics/equality.cmx engine/eConstr.cmx kernel/declarations.cmx \
    library/decl_kinds.cmx lib/dAst.cmx kernel/context.cmx \
    interp/constrintern.cmx interp/constrextern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx kernel/constr.cmx vernac/comFixpoint.cmx \
    vernac/comDefinition.cmx lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    plugins/funind/indfun.cmi
plugins/funind/indfun.cmi : vernac/vernacexpr.cmo proofs/tactypes.cmo \
    lib/pp.cmi kernel/names.cmi plugins/ltac/ltac_plugin.cmo lib/loc.cmi \
    proofs/goal.cmi engine/evd.cmi engine/eConstr.cmi
plugins/funind/indfun_common.cmo : vernac/vernacstate.cmi engine/univGen.cmi \
    tactics/tactics.cmi library/summary.cmi proofs/refiner.cmi \
    engine/proofview.cmi proofs/proof_global.cmi printing/printer.cmi \
    lib/pp.cmi proofs/pfedit.cmi clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    kernel/mod_subst.cmi library/libobject.cmi library/libnames.cmi \
    library/lib.cmi vernac/lemmas.cmi library/kindops.cmi clib/int.cmi \
    interp/impargs.cmi library/goptions.cmi library/globnames.cmi \
    library/global.cmi pretyping/glob_term.cmo lib/future.cmi lib/flags.cmi \
    clib/exninfo.cmi tactics/equality.cmi kernel/environ.cmi \
    kernel/entries.cmo engine/eConstr.cmi interp/dumpglob.cmi \
    pretyping/detyping.cmi interp/declare.cmi library/decl_kinds.cmo \
    lib/dAst.cmi library/coqlib.cmi interp/constrintern.cmi \
    interp/constrextern.cmi kernel/constr.cmi lib/cErrors.cmi \
    clib/cEphemeron.cmi plugins/funind/indfun_common.cmi
plugins/funind/indfun_common.cmx : vernac/vernacstate.cmx engine/univGen.cmx \
    tactics/tactics.cmx library/summary.cmx proofs/refiner.cmx \
    engine/proofview.cmx proofs/proof_global.cmx printing/printer.cmx \
    lib/pp.cmx proofs/pfedit.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    kernel/mod_subst.cmx library/libobject.cmx library/libnames.cmx \
    library/lib.cmx vernac/lemmas.cmx library/kindops.cmx clib/int.cmx \
    interp/impargs.cmx library/goptions.cmx library/globnames.cmx \
    library/global.cmx pretyping/glob_term.cmx lib/future.cmx lib/flags.cmx \
    clib/exninfo.cmx tactics/equality.cmx kernel/environ.cmx \
    kernel/entries.cmx engine/eConstr.cmx interp/dumpglob.cmx \
    pretyping/detyping.cmx interp/declare.cmx library/decl_kinds.cmx \
    lib/dAst.cmx library/coqlib.cmx interp/constrintern.cmx \
    interp/constrextern.cmx kernel/constr.cmx lib/cErrors.cmx \
    clib/cEphemeron.cmx plugins/funind/indfun_common.cmi
plugins/funind/indfun_common.cmi : lib/util.cmi proofs/tacmach.cmi \
    kernel/safe_typing.cmi lib/pp.cmi kernel/names.cmi library/libnames.cmi \
    vernac/lemmas.cmi pretyping/glob_term.cmo engine/evd.cmi \
    kernel/entries.cmo engine/eConstr.cmi library/decl_kinds.cmo \
    kernel/constr.cmi clib/cEphemeron.cmi
plugins/funind/invfun.cmo : vernac/vernacexpr.cmo kernel/vars.cmi \
    lib/util.cmi engine/univGen.cmi pretyping/typing.cmi engine/termops.cmi \
    kernel/term.cmi proofs/tactypes.cmo tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacenv.cmi kernel/sorts.cmi lib/rtree.cmi \
    pretyping/reductionops.cmi interp/redops.cmi engine/proofview.cmi \
    proofs/proof_global.cmi printing/printer.cmi printing/ppconstr.cmi \
    lib/pp.cmi proofs/pfedit.cmi clib/option.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi plugins/ltac/ltac_plugin.cmo \
    pretyping/locusops.cmi pretyping/locus.cmo library/libnames.cmi \
    vernac/lemmas.cmi tactics/inv.cmi clib/int.cmi pretyping/indrec.cmi \
    plugins/funind/indfun_common.cmi library/globnames.cmi library/global.cmi \
    interp/genredexpr.cmo lib/future.cmi lib/flags.cmi lib/feedback.cmi \
    vernac/explainErr.cmi engine/evd.cmi tactics/equality.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    kernel/declareops.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    library/coqlib.cmi kernel/context.cmi interp/constrintern.cmi \
    kernel/constr.cmi lib/cErrors.cmi kernel/cClosure.cmi lib/cAst.cmi \
    plugins/funind/invfun.cmi
plugins/funind/invfun.cmx : vernac/vernacexpr.cmx kernel/vars.cmx \
    lib/util.cmx engine/univGen.cmx pretyping/typing.cmx engine/termops.cmx \
    kernel/term.cmx proofs/tactypes.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacenv.cmx kernel/sorts.cmx lib/rtree.cmx \
    pretyping/reductionops.cmx interp/redops.cmx engine/proofview.cmx \
    proofs/proof_global.cmx printing/printer.cmx printing/ppconstr.cmx \
    lib/pp.cmx proofs/pfedit.cmx clib/option.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx plugins/ltac/ltac_plugin.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx library/libnames.cmx \
    vernac/lemmas.cmx tactics/inv.cmx clib/int.cmx pretyping/indrec.cmx \
    plugins/funind/indfun_common.cmx library/globnames.cmx library/global.cmx \
    interp/genredexpr.cmx lib/future.cmx lib/flags.cmx lib/feedback.cmx \
    vernac/explainErr.cmx engine/evd.cmx tactics/equality.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    kernel/declareops.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    library/coqlib.cmx kernel/context.cmx interp/constrintern.cmx \
    kernel/constr.cmx lib/cErrors.cmx kernel/cClosure.cmx lib/cAst.cmx \
    plugins/funind/invfun.cmi
plugins/funind/invfun.cmi : proofs/tactypes.cmo kernel/sorts.cmi \
    kernel/names.cmi engine/evd.cmi kernel/evar.cmi kernel/entries.cmo \
    kernel/constr.cmi
plugins/funind/recdef.cmo : vernac/vernacexpr.cmo kernel/vars.cmi \
    lib/util.cmi engine/univGen.cmi pretyping/typing.cmi kernel/typeops.cmi \
    engine/termops.cmi kernel/term.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi pretyping/tacred.cmi \
    proofs/tacmach.cmi interp/smartlocate.cmi proofs/refiner.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi proofs/proof_global.cmi \
    proofs/proof.cmi printing/printer.cmi pretyping/pretyping.cmi \
    printing/ppconstr.cmi lib/pp.cmi proofs/pfedit.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo library/libnames.cmi \
    library/lib.cmi vernac/lemmas.cmi clib/int.cmi \
    plugins/funind/indfun_common.cmi tactics/hints.cmi proofs/goal.cmi \
    library/globnames.cmi library/global.cmi pretyping/glob_term.cmo \
    interp/genredexpr.cmo lib/flags.cmi lib/feedback.cmi \
    plugins/extraction/extraction_plugin.cmo vernac/explainErr.cmi \
    engine/evd.cmi engine/evarutil.cmi tactics/equality.cmi \
    kernel/environ.cmi kernel/entries.cmo tactics/elim.cmi tactics/eauto.cmi \
    engine/eConstr.cmi interp/declare.cmi kernel/declarations.cmo \
    library/decl_kinds.cmo lib/dAst.cmi library/coqlib.cmi kernel/context.cmi \
    interp/constrintern.cmi kernel/constr.cmi lib/cErrors.cmi \
    kernel/cClosure.cmi lib/cAst.cmi tactics/auto.cmi \
    plugins/funind/recdef.cmi
plugins/funind/recdef.cmx : vernac/vernacexpr.cmx kernel/vars.cmx \
    lib/util.cmx engine/univGen.cmx pretyping/typing.cmx kernel/typeops.cmx \
    engine/termops.cmx kernel/term.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx pretyping/tacred.cmx \
    proofs/tacmach.cmx interp/smartlocate.cmx proofs/refiner.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx proofs/proof_global.cmx \
    proofs/proof.cmx printing/printer.cmx pretyping/pretyping.cmx \
    printing/ppconstr.cmx lib/pp.cmx proofs/pfedit.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx library/libnames.cmx \
    library/lib.cmx vernac/lemmas.cmx clib/int.cmx \
    plugins/funind/indfun_common.cmx tactics/hints.cmx proofs/goal.cmx \
    library/globnames.cmx library/global.cmx pretyping/glob_term.cmx \
    interp/genredexpr.cmx lib/flags.cmx lib/feedback.cmx \
    plugins/extraction/extraction_plugin.cmx vernac/explainErr.cmx \
    engine/evd.cmx engine/evarutil.cmx tactics/equality.cmx \
    kernel/environ.cmx kernel/entries.cmx tactics/elim.cmx tactics/eauto.cmx \
    engine/eConstr.cmx interp/declare.cmx kernel/declarations.cmx \
    library/decl_kinds.cmx lib/dAst.cmx library/coqlib.cmx kernel/context.cmx \
    interp/constrintern.cmx kernel/constr.cmx lib/cErrors.cmx \
    kernel/cClosure.cmx lib/cAst.cmx tactics/auto.cmx \
    plugins/funind/recdef.cmi
plugins/funind/recdef.cmi : proofs/tacmach.cmi kernel/names.cmi \
    plugins/funind/indfun_common.cmi engine/eConstr.cmi \
    interp/constrintern.cmi interp/constrexpr.cmo kernel/constr.cmi
plugins/ltac/coretactics.cmo : lib/util.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi \
    plugins/ltac/tacentries.cmi plugins/ltac/tacarg.cmi interp/stdarg.cmi \
    interp/redops.cmi engine/proofview.cmi lib/pp.cmi kernel/names.cmi \
    vernac/mltop.cmi proofs/logic.cmi pretyping/locus.cmo lib/loc.cmi \
    interp/genredexpr.cmo lib/genarg.cmi plugins/ltac/extraargs.cmi \
    parsing/extend.cmo tactics/elim.cmi lib/cAst.cmi
plugins/ltac/coretactics.cmx : lib/util.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx \
    plugins/ltac/tacentries.cmx plugins/ltac/tacarg.cmx interp/stdarg.cmx \
    interp/redops.cmx engine/proofview.cmx lib/pp.cmx kernel/names.cmx \
    vernac/mltop.cmx proofs/logic.cmx pretyping/locus.cmx lib/loc.cmx \
    interp/genredexpr.cmx lib/genarg.cmx plugins/ltac/extraargs.cmx \
    parsing/extend.cmx tactics/elim.cmx lib/cAst.cmx
plugins/ltac/evar_tactics.cmo : lib/util.cmi pretyping/typing.cmi \
    engine/termops.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi plugins/ltac/tacinterp.cmi plugins/ltac/tacexpr.cmi \
    proofs/refiner.cmi engine/proofview.cmi lib/pp.cmi kernel/names.cmi \
    engine/namegen.cmi pretyping/ltac_pretype.cmo pretyping/locusops.cmi \
    pretyping/locus.cmo lib/loc.cmi pretyping/geninterp.cmi engine/evd.cmi \
    engine/evarutil.cmi proofs/evar_refiner.cmi engine/evar_kinds.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi plugins/ltac/evar_tactics.cmi
plugins/ltac/evar_tactics.cmx : lib/util.cmx pretyping/typing.cmx \
    engine/termops.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx plugins/ltac/tacinterp.cmx plugins/ltac/tacexpr.cmx \
    proofs/refiner.cmx engine/proofview.cmx lib/pp.cmx kernel/names.cmx \
    engine/namegen.cmx pretyping/ltac_pretype.cmx pretyping/locusops.cmx \
    pretyping/locus.cmx lib/loc.cmx pretyping/geninterp.cmx engine/evd.cmx \
    engine/evarutil.cmx proofs/evar_refiner.cmx engine/evar_kinds.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx plugins/ltac/evar_tactics.cmi
plugins/ltac/evar_tactics.cmi : plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacexpr.cmi engine/proofview.cmi kernel/names.cmi \
    pretyping/locus.cmo pretyping/glob_term.cmo engine/eConstr.cmi
plugins/ltac/extraargs.cmo : lib/util.cmi parsing/tok.cmi \
    plugins/ltac/tacsubst.cmi proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacentries.cmi plugins/ltac/taccoerce.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi kernel/retroknowledge.cmi \
    engine/proofview.cmi printing/printer.cmi pretyping/pretyping.cmi \
    plugins/ltac/pptactic.cmi printing/ppconstr.cmi lib/pp.cmi \
    plugins/ltac/pltac.cmi proofs/pfedit.cmi parsing/pcoq.cmi \
    parsing/notation_gram.cmo kernel/names.cmi vernac/mltop.cmi \
    vernac/metasyntax.cmi pretyping/locus.cmo pretyping/geninterp.cmi \
    interp/genintern.cmi lib/genarg.cmi engine/ftactic.cmi parsing/extend.cmo \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi \
    plugins/ltac/extraargs.cmi
plugins/ltac/extraargs.cmx : lib/util.cmx parsing/tok.cmx \
    plugins/ltac/tacsubst.cmx proofs/tacmach.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacentries.cmx plugins/ltac/taccoerce.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx kernel/retroknowledge.cmx \
    engine/proofview.cmx printing/printer.cmx pretyping/pretyping.cmx \
    plugins/ltac/pptactic.cmx printing/ppconstr.cmx lib/pp.cmx \
    plugins/ltac/pltac.cmx proofs/pfedit.cmx parsing/pcoq.cmx \
    parsing/notation_gram.cmx kernel/names.cmx vernac/mltop.cmx \
    vernac/metasyntax.cmx pretyping/locus.cmx pretyping/geninterp.cmx \
    interp/genintern.cmx lib/genarg.cmx engine/ftactic.cmx parsing/extend.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx \
    plugins/ltac/extraargs.cmi
plugins/ltac/extraargs.cmi : plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacexpr.cmi kernel/retroknowledge.cmi lib/pp.cmi \
    parsing/pcoq.cmi parsing/notation_gram.cmo kernel/names.cmi \
    pretyping/locus.cmo pretyping/glob_term.cmo pretyping/geninterp.cmi \
    lib/genarg.cmi engine/eConstr.cmi interp/constrexpr.cmo
plugins/ltac/extratactics.cmo : vernac/vernacinterp.cmi \
    vernac/vernacexpr.cmo vernac/vernacentries.cmi stm/vernac_classifier.cmi \
    kernel/vars.cmi lib/util.cmi kernel/univ.cmi engine/uState.cmi \
    engine/termops.cmi proofs/tactypes.cmo tactics/tactics.cmi \
    tactics/tacticals.cmi plugins/ltac/tacsubst.cmi pretyping/tacred.cmi \
    proofs/tacmach.cmi plugins/ltac/tacinterp.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacentries.cmi \
    plugins/ltac/tacarg.cmi library/summary.cmi interp/stdarg.cmi \
    kernel/sorts.cmi pretyping/retyping.cmi proofs/refine.cmi \
    engine/proofview.cmi proofs/proof_global.cmi proofs/proof.cmi \
    printing/printer.cmi pretyping/pretyping.cmi pretyping/pretype_errors.cmi \
    printing/pputils.cmi plugins/ltac/pptactic.cmi lib/pp.cmi \
    plugins/ltac/pltac.cmi proofs/pfedit.cmi parsing/pcoq.cmi clib/option.cmi \
    kernel/names.cmi engine/namegen.cmi kernel/mod_subst.cmi vernac/mltop.cmi \
    pretyping/locus.cmo lib/loc.cmi library/libobject.cmi library/lib.cmi \
    tactics/leminv.cmi library/keys.cmi tactics/inv.cmi clib/int.cmi \
    library/global.cmi pretyping/glob_term.cmo pretyping/glob_ops.cmi \
    pretyping/geninterp.cmi interp/genintern.cmi lib/genarg.cmi \
    engine/ftactic.cmi pretyping/find_subterm.cmi lib/feedback.cmi \
    plugins/ltac/extraargs.cmi parsing/extend.cmo engine/evd.cmi \
    engine/evarutil.cmi plugins/ltac/evar_tactics.cmi engine/evar_kinds.cmi \
    tactics/equality.cmi tactics/elim.cmi engine/eConstr.cmi \
    pretyping/detyping.cmi interp/declare.cmi lib/dAst.cmi library/coqlib.cmi \
    tactics/contradiction.cmi interp/constrintern.cmi \
    interp/constrexpr_ops.cmi kernel/constr.cmi lib/cWarnings.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi tactics/autorewrite.cmi \
    plugins/ltac/extratactics.cmi
plugins/ltac/extratactics.cmx : vernac/vernacinterp.cmx \
    vernac/vernacexpr.cmx vernac/vernacentries.cmx stm/vernac_classifier.cmx \
    kernel/vars.cmx lib/util.cmx kernel/univ.cmx engine/uState.cmx \
    engine/termops.cmx proofs/tactypes.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx plugins/ltac/tacsubst.cmx pretyping/tacred.cmx \
    proofs/tacmach.cmx plugins/ltac/tacinterp.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacentries.cmx \
    plugins/ltac/tacarg.cmx library/summary.cmx interp/stdarg.cmx \
    kernel/sorts.cmx pretyping/retyping.cmx proofs/refine.cmx \
    engine/proofview.cmx proofs/proof_global.cmx proofs/proof.cmx \
    printing/printer.cmx pretyping/pretyping.cmx pretyping/pretype_errors.cmx \
    printing/pputils.cmx plugins/ltac/pptactic.cmx lib/pp.cmx \
    plugins/ltac/pltac.cmx proofs/pfedit.cmx parsing/pcoq.cmx clib/option.cmx \
    kernel/names.cmx engine/namegen.cmx kernel/mod_subst.cmx vernac/mltop.cmx \
    pretyping/locus.cmx lib/loc.cmx library/libobject.cmx library/lib.cmx \
    tactics/leminv.cmx library/keys.cmx tactics/inv.cmx clib/int.cmx \
    library/global.cmx pretyping/glob_term.cmx pretyping/glob_ops.cmx \
    pretyping/geninterp.cmx interp/genintern.cmx lib/genarg.cmx \
    engine/ftactic.cmx pretyping/find_subterm.cmx lib/feedback.cmx \
    plugins/ltac/extraargs.cmx parsing/extend.cmx engine/evd.cmx \
    engine/evarutil.cmx plugins/ltac/evar_tactics.cmx engine/evar_kinds.cmx \
    tactics/equality.cmx tactics/elim.cmx engine/eConstr.cmx \
    pretyping/detyping.cmx interp/declare.cmx lib/dAst.cmx library/coqlib.cmx \
    tactics/contradiction.cmx interp/constrintern.cmx \
    interp/constrexpr_ops.cmx kernel/constr.cmx lib/cWarnings.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx tactics/autorewrite.cmx \
    plugins/ltac/extratactics.cmi
plugins/ltac/extratactics.cmi : plugins/ltac/tacexpr.cmi \
    engine/proofview.cmi kernel/names.cmi
plugins/ltac/g_auto.cmo : vernac/vernacinterp.cmi vernac/vernacentries.cmi \
    stm/vernac_classifier.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    plugins/ltac/tacsubst.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacentries.cmi interp/stdarg.cmi printing/printer.cmi \
    pretyping/pretyping.cmi plugins/ltac/pptactic.cmi printing/ppconstr.cmi \
    lib/pp.cmi plugins/ltac/pltac.cmi proofs/pfedit.cmi parsing/pcoq.cmi \
    vernac/mltop.cmi pretyping/locus.cmo vernac/locality.cmi \
    library/libnames.cmi tactics/hints.cmi pretyping/geninterp.cmi \
    interp/genintern.cmi lib/genarg.cmi engine/ftactic.cmi parsing/extend.cmo \
    tactics/eauto.cmi kernel/constr.cmi parsing/cLexer.cmi tactics/auto.cmi
plugins/ltac/g_auto.cmx : vernac/vernacinterp.cmx vernac/vernacentries.cmx \
    stm/vernac_classifier.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    plugins/ltac/tacsubst.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacentries.cmx interp/stdarg.cmx printing/printer.cmx \
    pretyping/pretyping.cmx plugins/ltac/pptactic.cmx printing/ppconstr.cmx \
    lib/pp.cmx plugins/ltac/pltac.cmx proofs/pfedit.cmx parsing/pcoq.cmx \
    vernac/mltop.cmx pretyping/locus.cmx vernac/locality.cmx \
    library/libnames.cmx tactics/hints.cmx pretyping/geninterp.cmx \
    interp/genintern.cmx lib/genarg.cmx engine/ftactic.cmx parsing/extend.cmx \
    tactics/eauto.cmx kernel/constr.cmx parsing/cLexer.cmx tactics/auto.cmx
plugins/ltac/g_class.cmo : vernac/vernacentries.cmi \
    stm/vernac_classifier.cmi tactics/tacticals.cmi plugins/ltac/tacsubst.cmi \
    pretyping/tacred.cmi proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacentries.cmi plugins/ltac/tacarg.cmi interp/stdarg.cmi \
    interp/smartlocate.cmi engine/proofview.cmi plugins/ltac/pptactic.cmi \
    lib/pp.cmi parsing/pcoq.cmi clib/option.cmi vernac/mltop.cmi \
    vernac/locality.cmi tactics/hints.cmi library/global.cmi \
    pretyping/geninterp.cmi interp/genintern.cmi lib/genarg.cmi \
    engine/ftactic.cmi parsing/extend.cmo kernel/evar.cmi engine/eConstr.cmi \
    kernel/constr.cmi vernac/classes.cmi tactics/class_tactics.cmi \
    parsing/cLexer.cmi
plugins/ltac/g_class.cmx : vernac/vernacentries.cmx \
    stm/vernac_classifier.cmx tactics/tacticals.cmx plugins/ltac/tacsubst.cmx \
    pretyping/tacred.cmx proofs/tacmach.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacentries.cmx plugins/ltac/tacarg.cmx interp/stdarg.cmx \
    interp/smartlocate.cmx engine/proofview.cmx plugins/ltac/pptactic.cmx \
    lib/pp.cmx parsing/pcoq.cmx clib/option.cmx vernac/mltop.cmx \
    vernac/locality.cmx tactics/hints.cmx library/global.cmx \
    pretyping/geninterp.cmx interp/genintern.cmx lib/genarg.cmx \
    engine/ftactic.cmx parsing/extend.cmx kernel/evar.cmx engine/eConstr.cmx \
    kernel/constr.cmx vernac/classes.cmx tactics/class_tactics.cmx \
    parsing/cLexer.cmx
plugins/ltac/g_eqdecide.cmo : plugins/ltac/tacentries.cmi interp/stdarg.cmi \
    vernac/mltop.cmi lib/genarg.cmi parsing/extend.cmo tactics/eqdecide.cmi
plugins/ltac/g_eqdecide.cmx : plugins/ltac/tacentries.cmx interp/stdarg.cmx \
    vernac/mltop.cmx lib/genarg.cmx parsing/extend.cmx tactics/eqdecide.cmx
plugins/ltac/g_ltac.cmo : vernac/vernacinterp.cmi vernac/vernacexpr.cmo \
    vernac/vernacentries.cmi stm/vernac_classifier.cmi lib/util.cmi \
    parsing/tok.cmi plugins/ltac/tacinterp.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacentries.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi vernac/pvernac.cmi \
    proofs/proof_global.cmi proofs/proof.cmi plugins/ltac/pptactic.cmi \
    lib/pp.cmi plugins/ltac/pltac.cmi proofs/pfedit.cmi parsing/pcoq.cmi \
    clib/option.cmi kernel/names.cmi engine/namegen.cmi vernac/mltop.cmi \
    pretyping/locus.cmo vernac/locality.cmi lib/loc.cmi library/libnames.cmi \
    tactics/hints.cmi library/goptions.cmi proofs/goal_select.cmi \
    pretyping/glob_term.cmo interp/genredexpr.cmo lib/genarg.cmi \
    vernac/g_vernac.cmo vernac/g_proofs.cmo lib/feedback.cmi \
    parsing/extend.cmo interp/constrexpr.cmo kernel/constr.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi
plugins/ltac/g_ltac.cmx : vernac/vernacinterp.cmx vernac/vernacexpr.cmx \
    vernac/vernacentries.cmx stm/vernac_classifier.cmx lib/util.cmx \
    parsing/tok.cmx plugins/ltac/tacinterp.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacentries.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx vernac/pvernac.cmx \
    proofs/proof_global.cmx proofs/proof.cmx plugins/ltac/pptactic.cmx \
    lib/pp.cmx plugins/ltac/pltac.cmx proofs/pfedit.cmx parsing/pcoq.cmx \
    clib/option.cmx kernel/names.cmx engine/namegen.cmx vernac/mltop.cmx \
    pretyping/locus.cmx vernac/locality.cmx lib/loc.cmx library/libnames.cmx \
    tactics/hints.cmx library/goptions.cmx proofs/goal_select.cmx \
    pretyping/glob_term.cmx interp/genredexpr.cmx lib/genarg.cmx \
    vernac/g_vernac.cmx vernac/g_proofs.cmx lib/feedback.cmx \
    parsing/extend.cmx interp/constrexpr.cmx kernel/constr.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx
plugins/ltac/g_obligations.cmo : vernac/vernacinterp.cmi \
    vernac/vernacexpr.cmo vernac/vernacentries.cmi stm/vernac_classifier.cmi \
    plugins/ltac/tactic_option.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi engine/proofview.cmi \
    plugins/ltac/pptactic.cmi lib/pp.cmi plugins/ltac/pltac.cmi \
    parsing/pcoq.cmi vernac/obligations.cmi vernac/locality.cmi \
    library/libnames.cmi library/global.cmi interp/genintern.cmi \
    lib/genarg.cmi lib/feedback.cmi plugins/ltac/extraargs.cmi \
    parsing/extend.cmo interp/constrexpr_ops.cmi interp/constrexpr.cmo \
    kernel/constr.cmi
plugins/ltac/g_obligations.cmx : vernac/vernacinterp.cmx \
    vernac/vernacexpr.cmx vernac/vernacentries.cmx stm/vernac_classifier.cmx \
    plugins/ltac/tactic_option.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx engine/proofview.cmx \
    plugins/ltac/pptactic.cmx lib/pp.cmx plugins/ltac/pltac.cmx \
    parsing/pcoq.cmx vernac/obligations.cmx vernac/locality.cmx \
    library/libnames.cmx library/global.cmx interp/genintern.cmx \
    lib/genarg.cmx lib/feedback.cmx plugins/ltac/extraargs.cmx \
    parsing/extend.cmx interp/constrexpr_ops.cmx interp/constrexpr.cmx \
    kernel/constr.cmx
plugins/ltac/g_rewrite.cmo : vernac/vernacinterp.cmi vernac/vernacexpr.cmo \
    vernac/vernacentries.cmi stm/vernac_classifier.cmi proofs/tactypes.cmo \
    tactics/tacticals.cmi plugins/ltac/tacsubst.cmi proofs/tacmach.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacentries.cmi interp/stdarg.cmi plugins/ltac/rewrite.cmi \
    vernac/pvernac.cmi engine/proofview.cmi printing/printer.cmi \
    printing/pputils.cmi plugins/ltac/pptactic.cmi printing/ppconstr.cmi \
    lib/pp.cmi plugins/ltac/pltac.cmi proofs/pfedit.cmi parsing/pcoq.cmi \
    kernel/names.cmi vernac/mltop.cmi pretyping/locus.cmo vernac/locality.cmi \
    library/libnames.cmi pretyping/glob_term.cmo pretyping/geninterp.cmi \
    interp/genintern.cmi lib/genarg.cmi engine/ftactic.cmi lib/feedback.cmi \
    plugins/ltac/extraargs.cmi parsing/extend.cmo lib/dAst.cmi \
    interp/constrexpr.cmo parsing/cLexer.cmi tactics/autorewrite.cmi
plugins/ltac/g_rewrite.cmx : vernac/vernacinterp.cmx vernac/vernacexpr.cmx \
    vernac/vernacentries.cmx stm/vernac_classifier.cmx proofs/tactypes.cmx \
    tactics/tacticals.cmx plugins/ltac/tacsubst.cmx proofs/tacmach.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacentries.cmx interp/stdarg.cmx plugins/ltac/rewrite.cmx \
    vernac/pvernac.cmx engine/proofview.cmx printing/printer.cmx \
    printing/pputils.cmx plugins/ltac/pptactic.cmx printing/ppconstr.cmx \
    lib/pp.cmx plugins/ltac/pltac.cmx proofs/pfedit.cmx parsing/pcoq.cmx \
    kernel/names.cmx vernac/mltop.cmx pretyping/locus.cmx vernac/locality.cmx \
    library/libnames.cmx pretyping/glob_term.cmx pretyping/geninterp.cmx \
    interp/genintern.cmx lib/genarg.cmx engine/ftactic.cmx lib/feedback.cmx \
    plugins/ltac/extraargs.cmx parsing/extend.cmx lib/dAst.cmx \
    interp/constrexpr.cmx parsing/cLexer.cmx tactics/autorewrite.cmx
plugins/ltac/g_tactic.cmo : lib/util.cmi parsing/tok.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi plugins/ltac/tacexpr.cmi interp/redops.cmi \
    vernac/pvernac.cmi lib/pp.cmi plugins/ltac/pltac.cmi parsing/pcoq.cmi \
    clib/option.cmi kernel/names.cmi engine/namegen.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo lib/loc.cmi \
    library/libnames.cmi tactics/inv.cmi clib/int.cmi interp/genredexpr.cmo \
    plugins/ltac/extraargs.cmi parsing/extend.cmo engine/evar_kinds.cmi \
    tactics/equality.cmi library/decl_kinds.cmo interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo kernel/constr.cmi lib/cWarnings.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi
plugins/ltac/g_tactic.cmx : lib/util.cmx parsing/tok.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx plugins/ltac/tacexpr.cmx interp/redops.cmx \
    vernac/pvernac.cmx lib/pp.cmx plugins/ltac/pltac.cmx parsing/pcoq.cmx \
    clib/option.cmx kernel/names.cmx engine/namegen.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx lib/loc.cmx \
    library/libnames.cmx tactics/inv.cmx clib/int.cmx interp/genredexpr.cmx \
    plugins/ltac/extraargs.cmx parsing/extend.cmx engine/evar_kinds.cmx \
    tactics/equality.cmx library/decl_kinds.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx kernel/constr.cmx lib/cWarnings.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx
plugins/ltac/pltac.cmo : plugins/ltac/tacarg.cmi interp/stdarg.cmi \
    parsing/pcoq.cmi plugins/ltac/pltac.cmi
plugins/ltac/pltac.cmx : plugins/ltac/tacarg.cmx interp/stdarg.cmx \
    parsing/pcoq.cmx plugins/ltac/pltac.cmi
plugins/ltac/pltac.cmi : proofs/tactypes.cmo tactics/tactics.cmi \
    plugins/ltac/tacexpr.cmi parsing/pcoq.cmi kernel/names.cmi \
    pretyping/locus.cmo library/libnames.cmi interp/genredexpr.cmo \
    interp/constrexpr.cmo lib/cAst.cmi
plugins/ltac/pptactic.cmo : lib/util.cmi engine/termops.cmi \
    proofs/tactypes.cmo tactics/tactics.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacenv.cmi plugins/ltac/tacarg.cmi library/summary.cmi \
    interp/stdarg.cmi printing/printer.cmi printing/pputils.cmi \
    printing/ppconstr.cmi lib/pp.cmi proofs/pfedit.cmi clib/option.cmi \
    parsing/notation_gram.cmo library/nametab.cmi kernel/names.cmi \
    engine/namegen.cmi proofs/miscprint.cmi pretyping/locusops.cmi \
    pretyping/locus.cmo lib/loc.cmi tactics/inv.cmi clib/int.cmi \
    proofs/goal_select.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo interp/genredexpr.cmo printing/genprint.cmi \
    pretyping/geninterp.cmi lib/genarg.cmi lib/flags.cmi parsing/extend.cmo \
    engine/evd.cmi tactics/equality.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo lib/dAst.cmi interp/constrexpr.cmo \
    kernel/constr.cmi lib/cErrors.cmi lib/cAst.cmi plugins/ltac/pptactic.cmi
plugins/ltac/pptactic.cmx : lib/util.cmx engine/termops.cmx \
    proofs/tactypes.cmx tactics/tactics.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacenv.cmx plugins/ltac/tacarg.cmx library/summary.cmx \
    interp/stdarg.cmx printing/printer.cmx printing/pputils.cmx \
    printing/ppconstr.cmx lib/pp.cmx proofs/pfedit.cmx clib/option.cmx \
    parsing/notation_gram.cmx library/nametab.cmx kernel/names.cmx \
    engine/namegen.cmx proofs/miscprint.cmx pretyping/locusops.cmx \
    pretyping/locus.cmx lib/loc.cmx tactics/inv.cmx clib/int.cmx \
    proofs/goal_select.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx interp/genredexpr.cmx printing/genprint.cmx \
    pretyping/geninterp.cmx lib/genarg.cmx lib/flags.cmx parsing/extend.cmx \
    engine/evd.cmx tactics/equality.cmx engine/eConstr.cmx \
    library/decl_kinds.cmx lib/dAst.cmx interp/constrexpr.cmx \
    kernel/constr.cmx lib/cErrors.cmx lib/cAst.cmx plugins/ltac/pptactic.cmi
plugins/ltac/pptactic.cmi : proofs/tactypes.cmo plugins/ltac/tacexpr.cmi \
    interp/stdarg.cmi lib/pp.cmi parsing/notation_gram.cmo kernel/names.cmi \
    pretyping/locus.cmo lib/loc.cmi proofs/goal_select.cmi \
    interp/genredexpr.cmo printing/genprint.cmi pretyping/geninterp.cmi \
    lib/genarg.cmi parsing/extend.cmo engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi interp/constrexpr.cmo
plugins/ltac/profile_ltac.cmo : lib/xml_datatype.cmi lib/util.cmi \
    clib/unicode.cmi plugins/ltac/tacexpr.cmi lib/system.cmi \
    library/summary.cmi stm/stm.cmi lib/stateid.cmi engine/proofview.cmi \
    printing/printer.cmi plugins/ltac/pptactic.cmi lib/pp.cmi \
    kernel/names.cmi lib/loc.cmi library/goptions.cmi library/global.cmi \
    lib/flags.cmi lib/feedback.cmi library/declaremods.cmi lib/cWarnings.cmi \
    clib/cString.cmi clib/cList.cmi lib/cErrors.cmi \
    plugins/ltac/profile_ltac.cmi
plugins/ltac/profile_ltac.cmx : lib/xml_datatype.cmi lib/util.cmx \
    clib/unicode.cmx plugins/ltac/tacexpr.cmx lib/system.cmx \
    library/summary.cmx stm/stm.cmx lib/stateid.cmx engine/proofview.cmx \
    printing/printer.cmx plugins/ltac/pptactic.cmx lib/pp.cmx \
    kernel/names.cmx lib/loc.cmx library/goptions.cmx library/global.cmx \
    lib/flags.cmx lib/feedback.cmx library/declaremods.cmx lib/cWarnings.cmx \
    clib/cString.cmx clib/cList.cmx lib/cErrors.cmx \
    plugins/ltac/profile_ltac.cmi
plugins/ltac/profile_ltac.cmi : plugins/ltac/tacexpr.cmi \
    engine/proofview.cmi clib/cString.cmi
plugins/ltac/profile_ltac_tactics.cmo : vernac/vernacentries.cmi \
    stm/vernac_classifier.cmi plugins/ltac/tacentries.cmi interp/stdarg.cmi \
    engine/proofview.cmi plugins/ltac/profile_ltac.cmi vernac/mltop.cmi \
    lib/genarg.cmi lib/flags.cmi parsing/extend.cmo
plugins/ltac/profile_ltac_tactics.cmx : vernac/vernacentries.cmx \
    stm/vernac_classifier.cmx plugins/ltac/tacentries.cmx interp/stdarg.cmx \
    engine/proofview.cmx plugins/ltac/profile_ltac.cmx vernac/mltop.cmx \
    lib/genarg.cmx lib/flags.cmx parsing/extend.cmx
plugins/ltac/rewrite.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    pretyping/unification.cmi engine/uState.cmi pretyping/typing.cmi \
    pretyping/typeclasses.cmi engine/termops.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi pretyping/tacred.cmi \
    proofs/tacmach.cmi plugins/ltac/tacinterp.cmi plugins/ltac/tacexpr.cmi \
    kernel/sorts.cmi pretyping/retyping.cmi proofs/refiner.cmi \
    proofs/refine.cmi pretyping/reductionops.cmi kernel/reduction.cmi \
    proofs/redexpr.cmi engine/proofview.cmi printing/printer.cmi \
    pretyping/pretyping.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    proofs/pfedit.cmi clib/option.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi proofs/logic.cmi pretyping/locusops.cmi \
    pretyping/locus.cmo vernac/locality.cmi lib/loc.cmi library/libnames.cmi \
    library/lib.cmi vernac/lemmas.cmi clib/int.cmi pretyping/inductiveops.cmi \
    tactics/ind_tables.cmi lib/hook.cmi tactics/hipattern.cmi \
    tactics/hints.cmi vernac/himsg.cmi library/globnames.cmi \
    library/global.cmi pretyping/geninterp.cmi lib/genarg.cmi \
    engine/ftactic.cmi lib/flags.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarconv.cmi kernel/evar.cmi tactics/equality.cmi \
    kernel/environ.cmi kernel/entries.cmo tactics/elimschemes.cmi \
    engine/eConstr.cmi interp/declare.cmi library/decl_kinds.cmo \
    library/coqlib.cmi lib/control.cmi kernel/context.cmi \
    interp/constrintern.cmi interp/constrexpr.cmo kernel/constr.cmi \
    proofs/clenv.cmi vernac/classes.cmi tactics/class_tactics.cmi \
    lib/cWarnings.cmi lib/cErrors.cmi kernel/cClosure.cmi lib/cAst.cmi \
    tactics/autorewrite.cmi plugins/ltac/rewrite.cmi
plugins/ltac/rewrite.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    pretyping/unification.cmx engine/uState.cmx pretyping/typing.cmx \
    pretyping/typeclasses.cmx engine/termops.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx pretyping/tacred.cmx \
    proofs/tacmach.cmx plugins/ltac/tacinterp.cmx plugins/ltac/tacexpr.cmx \
    kernel/sorts.cmx pretyping/retyping.cmx proofs/refiner.cmx \
    proofs/refine.cmx pretyping/reductionops.cmx kernel/reduction.cmx \
    proofs/redexpr.cmx engine/proofview.cmx printing/printer.cmx \
    pretyping/pretyping.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    proofs/pfedit.cmx clib/option.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx proofs/logic.cmx pretyping/locusops.cmx \
    pretyping/locus.cmx vernac/locality.cmx lib/loc.cmx library/libnames.cmx \
    library/lib.cmx vernac/lemmas.cmx clib/int.cmx pretyping/inductiveops.cmx \
    tactics/ind_tables.cmx lib/hook.cmx tactics/hipattern.cmx \
    tactics/hints.cmx vernac/himsg.cmx library/globnames.cmx \
    library/global.cmx pretyping/geninterp.cmx lib/genarg.cmx \
    engine/ftactic.cmx lib/flags.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarconv.cmx kernel/evar.cmx tactics/equality.cmx \
    kernel/environ.cmx kernel/entries.cmx tactics/elimschemes.cmx \
    engine/eConstr.cmx interp/declare.cmx library/decl_kinds.cmx \
    library/coqlib.cmx lib/control.cmx kernel/context.cmx \
    interp/constrintern.cmx interp/constrexpr.cmx kernel/constr.cmx \
    proofs/clenv.cmx vernac/classes.cmx tactics/class_tactics.cmx \
    lib/cWarnings.cmx lib/cErrors.cmx kernel/cClosure.cmx lib/cAst.cmx \
    tactics/autorewrite.cmx plugins/ltac/rewrite.cmi
plugins/ltac/rewrite.cmi : proofs/tactypes.cmo plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacexpr.cmi engine/proofview.cmi lib/pp.cmi kernel/names.cmi \
    pretyping/locus.cmo engine/evd.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi interp/constrexpr.cmo kernel/constr.cmi
plugins/ltac/tacarg.cmo : plugins/ltac/tacexpr.cmi interp/stdarg.cmi \
    pretyping/geninterp.cmi lib/genarg.cmi plugins/ltac/tacarg.cmi
plugins/ltac/tacarg.cmx : plugins/ltac/tacexpr.cmx interp/stdarg.cmx \
    pretyping/geninterp.cmx lib/genarg.cmx plugins/ltac/tacarg.cmi
plugins/ltac/tacarg.cmi : proofs/tactypes.cmo tactics/tactics.cmi \
    plugins/ltac/tacexpr.cmi pretyping/geninterp.cmi lib/genarg.cmi \
    engine/eConstr.cmi interp/constrexpr.cmo lib/cAst.cmi
plugins/ltac/taccoerce.cmo : lib/util.cmi engine/termops.cmi \
    proofs/tactypes.cmo pretyping/tacred.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi kernel/sorts.cmi \
    printing/printer.cmi plugins/ltac/pptactic.cmi lib/pp.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi engine/namegen.cmi \
    pretyping/ltac_pretype.cmo pretyping/locus.cmo library/globnames.cmi \
    printing/genprint.cmi pretyping/geninterp.cmi lib/genarg.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/ltac/taccoerce.cmi
plugins/ltac/taccoerce.cmx : lib/util.cmx engine/termops.cmx \
    proofs/tactypes.cmx pretyping/tacred.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx kernel/sorts.cmx \
    printing/printer.cmx plugins/ltac/pptactic.cmx lib/pp.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx engine/namegen.cmx \
    pretyping/ltac_pretype.cmx pretyping/locus.cmx library/globnames.cmx \
    printing/genprint.cmx pretyping/geninterp.cmx lib/genarg.cmx \
    engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx kernel/constr.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/ltac/taccoerce.cmi
plugins/ltac/taccoerce.cmi : lib/util.cmi proofs/tactypes.cmo \
    plugins/ltac/tacexpr.cmi lib/pp.cmi kernel/names.cmi engine/namegen.cmi \
    pretyping/ltac_pretype.cmo pretyping/locus.cmo lib/loc.cmi \
    pretyping/geninterp.cmi lib/genarg.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi
plugins/ltac/tacentries.cmo : vernac/vernacexpr.cmo lib/util.cmi \
    plugins/ltac/tacsubst.cmi proofs/tacmach.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi \
    plugins/ltac/taccoerce.cmi plugins/ltac/tacarg.cmi library/summary.cmi \
    interp/stdarg.cmi library/states.cmi engine/proofview.cmi \
    printing/prettyp.cmi plugins/ltac/pptactic.cmi lib/pp.cmi \
    plugins/ltac/pltac.cmi parsing/pcoq.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    kernel/mod_subst.cmi vernac/mltop.cmi pretyping/locus.cmo lib/loc.cmi \
    library/libobject.cmi library/libnames.cmi library/lib.cmi clib/int.cmi \
    library/global.cmi pretyping/geninterp.cmi lib/genarg.cmi lib/flags.cmi \
    lib/feedback.cmi parsing/extend.cmo vernac/egramml.cmi lib/cWarnings.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi \
    plugins/ltac/tacentries.cmi
plugins/ltac/tacentries.cmx : vernac/vernacexpr.cmx lib/util.cmx \
    plugins/ltac/tacsubst.cmx proofs/tacmach.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx \
    plugins/ltac/taccoerce.cmx plugins/ltac/tacarg.cmx library/summary.cmx \
    interp/stdarg.cmx library/states.cmx engine/proofview.cmx \
    printing/prettyp.cmx plugins/ltac/pptactic.cmx lib/pp.cmx \
    plugins/ltac/pltac.cmx parsing/pcoq.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    kernel/mod_subst.cmx vernac/mltop.cmx pretyping/locus.cmx lib/loc.cmx \
    library/libobject.cmx library/libnames.cmx library/lib.cmx clib/int.cmx \
    library/global.cmx pretyping/geninterp.cmx lib/genarg.cmx lib/flags.cmx \
    lib/feedback.cmx parsing/extend.cmx vernac/egramml.cmx lib/cWarnings.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx \
    plugins/ltac/tacentries.cmi
plugins/ltac/tacentries.cmi : vernac/vernacinterp.cmi vernac/vernacexpr.cmo \
    plugins/ltac/tacexpr.cmi engine/proofview.cmi plugins/ltac/pptactic.cmi \
    parsing/pcoq.cmi kernel/names.cmi lib/loc.cmi library/libnames.cmi \
    clib/int.cmi pretyping/geninterp.cmi lib/genarg.cmi parsing/extend.cmo
plugins/ltac/tacenv.cmo : vernac/vernacinterp.cmi lib/util.cmi \
    plugins/ltac/tacsubst.cmi plugins/ltac/tacexpr.cmi library/summary.cmi \
    engine/proofview.cmi lib/pp.cmi library/nametab.cmi kernel/names.cmi \
    kernel/mod_subst.cmi library/libobject.cmi library/libnames.cmi \
    library/lib.cmi pretyping/geninterp.cmi lib/cErrors.cmi \
    plugins/ltac/tacenv.cmi
plugins/ltac/tacenv.cmx : vernac/vernacinterp.cmx lib/util.cmx \
    plugins/ltac/tacsubst.cmx plugins/ltac/tacexpr.cmx library/summary.cmx \
    engine/proofview.cmx lib/pp.cmx library/nametab.cmx kernel/names.cmx \
    kernel/mod_subst.cmx library/libobject.cmx library/libnames.cmx \
    library/lib.cmx pretyping/geninterp.cmx lib/cErrors.cmx \
    plugins/ltac/tacenv.cmi
plugins/ltac/tacenv.cmi : vernac/vernacinterp.cmi plugins/ltac/tacexpr.cmi \
    engine/proofview.cmi library/nametab.cmi kernel/names.cmi \
    library/libnames.cmi pretyping/geninterp.cmi
plugins/ltac/tacexpr.cmo : proofs/tactypes.cmo tactics/tactics.cmi \
    interp/stdarg.cmi pretyping/pattern.cmo kernel/names.cmi \
    engine/namegen.cmi pretyping/ltac_pretype.cmo pretyping/locus.cmo \
    lib/loc.cmi library/libnames.cmi tactics/inv.cmi proofs/goal_select.cmi \
    pretyping/glob_term.cmo interp/genredexpr.cmo interp/genintern.cmi \
    lib/genarg.cmi engine/evd.cmi tactics/equality.cmi kernel/environ.cmi \
    engine/eConstr.cmi interp/constrexpr.cmo pretyping/constr_matching.cmi \
    lib/cAst.cmi plugins/ltac/tacexpr.cmi
plugins/ltac/tacexpr.cmx : proofs/tactypes.cmx tactics/tactics.cmx \
    interp/stdarg.cmx pretyping/pattern.cmx kernel/names.cmx \
    engine/namegen.cmx pretyping/ltac_pretype.cmx pretyping/locus.cmx \
    lib/loc.cmx library/libnames.cmx tactics/inv.cmx proofs/goal_select.cmx \
    pretyping/glob_term.cmx interp/genredexpr.cmx interp/genintern.cmx \
    lib/genarg.cmx engine/evd.cmx tactics/equality.cmx kernel/environ.cmx \
    engine/eConstr.cmx interp/constrexpr.cmx pretyping/constr_matching.cmx \
    lib/cAst.cmx plugins/ltac/tacexpr.cmi
plugins/ltac/tacexpr.cmi : proofs/tactypes.cmo tactics/tactics.cmi \
    interp/stdarg.cmi pretyping/pattern.cmo kernel/names.cmi \
    engine/namegen.cmi pretyping/ltac_pretype.cmo pretyping/locus.cmo \
    lib/loc.cmi library/libnames.cmi tactics/inv.cmi proofs/goal_select.cmi \
    pretyping/glob_term.cmo interp/genredexpr.cmo interp/genintern.cmi \
    lib/genarg.cmi engine/evd.cmi tactics/equality.cmi kernel/environ.cmi \
    engine/eConstr.cmi interp/constrexpr.cmo pretyping/constr_matching.cmi \
    lib/cAst.cmi
plugins/ltac/tacintern.cmo : vernac/vernacinterp.cmi lib/util.cmi \
    engine/termops.cmi proofs/tactypes.cmo tactics/tactics.cmi \
    pretyping/tacred.cmi plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi interp/smartlocate.cmi \
    pretyping/pretyping.cmi pretyping/pretype_errors.cmi \
    plugins/ltac/pptactic.cmi lib/pp.cmi pretyping/pattern.cmo \
    clib/option.cmi interp/notation.cmi library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi proofs/logic.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo lib/loc.cmi \
    library/libnames.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi interp/genredexpr.cmo \
    interp/genintern.cmi lib/genarg.cmi lib/flags.cmi engine/evd.cmi \
    kernel/environ.cmi interp/dumpglob.cmi lib/dAst.cmi \
    interp/constrintern.cmi interp/constrexpr.cmo lib/cWarnings.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/ltac/tacintern.cmi
plugins/ltac/tacintern.cmx : vernac/vernacinterp.cmx lib/util.cmx \
    engine/termops.cmx proofs/tactypes.cmx tactics/tactics.cmx \
    pretyping/tacred.cmx plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx interp/smartlocate.cmx \
    pretyping/pretyping.cmx pretyping/pretype_errors.cmx \
    plugins/ltac/pptactic.cmx lib/pp.cmx pretyping/pattern.cmx \
    clib/option.cmx interp/notation.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx proofs/logic.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx lib/loc.cmx \
    library/libnames.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx interp/genredexpr.cmx \
    interp/genintern.cmx lib/genarg.cmx lib/flags.cmx engine/evd.cmx \
    kernel/environ.cmx interp/dumpglob.cmx lib/dAst.cmx \
    interp/constrintern.cmx interp/constrexpr.cmx lib/cWarnings.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/ltac/tacintern.cmi
plugins/ltac/tacintern.cmi : proofs/tactypes.cmo plugins/ltac/tacexpr.cmi \
    lib/pp.cmi kernel/names.cmi library/libnames.cmi interp/genintern.cmi \
    lib/genarg.cmi kernel/environ.cmi interp/constrexpr.cmo
plugins/ltac/tacinterp.cmo : vernac/vernacentries.cmi lib/util.cmi \
    pretyping/typing.cmi engine/termops.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi \
    plugins/ltac/tactic_matching.cmi plugins/ltac/tactic_debug.cmi \
    pretyping/tacred.cmi proofs/tacmach.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi \
    plugins/ltac/taccoerce.cmi plugins/ltac/tacarg.cmi interp/stdarg.cmi \
    proofs/refiner.cmi proofs/redexpr.cmi engine/proofview.cmi \
    plugins/ltac/profile_ltac.cmi printing/printer.cmi \
    pretyping/pretyping.cmi plugins/ltac/pptactic.cmi lib/pp.cmi \
    proofs/pfedit.cmi pretyping/patternops.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi pretyping/ltac_pretype.cmo proofs/logic.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo lib/loc.cmi \
    library/libnames.cmi tactics/leminv.cmi tactics/inv.cmi lib/hook.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi interp/genredexpr.cmo \
    printing/genprint.cmi pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi engine/ftactic.cmi clib/exninfo.cmi engine/evd.cmi \
    tactics/equality.cmi kernel/environ.cmi engine/eConstr.cmi lib/dAst.cmi \
    lib/control.cmi kernel/context.cmi interp/constrintern.cmi \
    interp/constrexpr.cmo pretyping/constr_matching.cmi lib/cWarnings.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi \
    plugins/ltac/tacinterp.cmi
plugins/ltac/tacinterp.cmx : vernac/vernacentries.cmx lib/util.cmx \
    pretyping/typing.cmx engine/termops.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx \
    plugins/ltac/tactic_matching.cmx plugins/ltac/tactic_debug.cmx \
    pretyping/tacred.cmx proofs/tacmach.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx \
    plugins/ltac/taccoerce.cmx plugins/ltac/tacarg.cmx interp/stdarg.cmx \
    proofs/refiner.cmx proofs/redexpr.cmx engine/proofview.cmx \
    plugins/ltac/profile_ltac.cmx printing/printer.cmx \
    pretyping/pretyping.cmx plugins/ltac/pptactic.cmx lib/pp.cmx \
    proofs/pfedit.cmx pretyping/patternops.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx pretyping/ltac_pretype.cmx proofs/logic.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx lib/loc.cmx \
    library/libnames.cmx tactics/leminv.cmx tactics/inv.cmx lib/hook.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx interp/genredexpr.cmx \
    printing/genprint.cmx pretyping/geninterp.cmx interp/genintern.cmx \
    lib/genarg.cmx engine/ftactic.cmx clib/exninfo.cmx engine/evd.cmx \
    tactics/equality.cmx kernel/environ.cmx engine/eConstr.cmx lib/dAst.cmx \
    lib/control.cmx kernel/context.cmx interp/constrintern.cmx \
    interp/constrexpr.cmx pretyping/constr_matching.cmx lib/cWarnings.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx \
    plugins/ltac/tacinterp.cmi
plugins/ltac/tacinterp.cmi : proofs/tactypes.cmo \
    plugins/ltac/tactic_debug.cmi plugins/ltac/tacexpr.cmi clib/store.cmi \
    proofs/redexpr.cmi engine/proofview.cmi pretyping/pretyping.cmi \
    kernel/names.cmi pretyping/ltac_pretype.cmo pretyping/locus.cmo \
    pretyping/geninterp.cmi lib/genarg.cmi engine/ftactic.cmi \
    clib/exninfo.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi
plugins/ltac/tacsubst.cmo : lib/util.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi plugins/ltac/tacexpr.cmi plugins/ltac/tacarg.cmi \
    interp/stdarg.cmi interp/redops.cmi printing/printer.cmi lib/pp.cmi \
    proofs/pfedit.cmi pretyping/patternops.cmi clib/option.cmi \
    kernel/mod_subst.cmi pretyping/locus.cmo lib/loc.cmi \
    library/globnames.cmi interp/genredexpr.cmo interp/genintern.cmi \
    lib/genarg.cmi lib/feedback.cmi pretyping/detyping.cmi lib/cAst.cmi \
    plugins/ltac/tacsubst.cmi
plugins/ltac/tacsubst.cmx : lib/util.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx plugins/ltac/tacexpr.cmx plugins/ltac/tacarg.cmx \
    interp/stdarg.cmx interp/redops.cmx printing/printer.cmx lib/pp.cmx \
    proofs/pfedit.cmx pretyping/patternops.cmx clib/option.cmx \
    kernel/mod_subst.cmx pretyping/locus.cmx lib/loc.cmx \
    library/globnames.cmx interp/genredexpr.cmx interp/genintern.cmx \
    lib/genarg.cmx lib/feedback.cmx pretyping/detyping.cmx lib/cAst.cmx \
    plugins/ltac/tacsubst.cmi
plugins/ltac/tacsubst.cmi : proofs/tactypes.cmo plugins/ltac/tacexpr.cmi \
    kernel/mod_subst.cmi lib/genarg.cmi
plugins/ltac/tactic_debug.cmo : lib/util.cmi engine/termops.cmi \
    proofs/tacmach.cmi plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi \
    engine/proofview.cmi printing/printer.cmi plugins/ltac/pptactic.cmi \
    lib/pp.cmi proofs/pfedit.cmi clib/option.cmi kernel/names.cmi \
    pretyping/ltac_pretype.cmo proofs/logic.cmi lib/loc.cmi clib/int.cmi \
    library/goptions.cmi library/global.cmi vernac/explainErr.cmi \
    clib/exninfo.cmi clib/cList.cmi lib/cErrors.cmi \
    plugins/ltac/tactic_debug.cmi
plugins/ltac/tactic_debug.cmx : lib/util.cmx engine/termops.cmx \
    proofs/tacmach.cmx plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx \
    engine/proofview.cmx printing/printer.cmx plugins/ltac/pptactic.cmx \
    lib/pp.cmx proofs/pfedit.cmx clib/option.cmx kernel/names.cmx \
    pretyping/ltac_pretype.cmx proofs/logic.cmx lib/loc.cmx clib/int.cmx \
    library/goptions.cmx library/global.cmx vernac/explainErr.cmx \
    clib/exninfo.cmx clib/cList.cmx lib/cErrors.cmx \
    plugins/ltac/tactic_debug.cmi
plugins/ltac/tactic_debug.cmi : plugins/ltac/tacexpr.cmi \
    engine/proofview.cmi lib/pp.cmi pretyping/pattern.cmo kernel/names.cmi \
    lib/loc.cmi clib/exninfo.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi
plugins/ltac/tactic_matching.cmo : plugins/ltac/tacexpr.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi lib/pp.cmi \
    kernel/names.cmi pretyping/ltac_pretype.cmo clib/iStream.cmi \
    clib/exninfo.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/context.cmi pretyping/constr_matching.cmi clib/cList.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/ltac/tactic_matching.cmi
plugins/ltac/tactic_matching.cmx : plugins/ltac/tacexpr.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx lib/pp.cmx \
    kernel/names.cmx pretyping/ltac_pretype.cmx clib/iStream.cmx \
    clib/exninfo.cmx engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/context.cmx pretyping/constr_matching.cmx clib/cList.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/ltac/tactic_matching.cmi
plugins/ltac/tactic_matching.cmi : plugins/ltac/tacexpr.cmi \
    engine/proofview.cmi pretyping/pattern.cmo kernel/names.cmi \
    pretyping/ltac_pretype.cmo engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi pretyping/constr_matching.cmi
plugins/ltac/tactic_option.cmo : plugins/ltac/tacsubst.cmi \
    plugins/ltac/tacinterp.cmi plugins/ltac/tacexpr.cmi library/summary.cmi \
    plugins/ltac/pptactic.cmi lib/pp.cmi library/libobject.cmi \
    library/lib.cmi library/global.cmi plugins/ltac/tactic_option.cmi
plugins/ltac/tactic_option.cmx : plugins/ltac/tacsubst.cmx \
    plugins/ltac/tacinterp.cmx plugins/ltac/tacexpr.cmx library/summary.cmx \
    plugins/ltac/pptactic.cmx lib/pp.cmx library/libobject.cmx \
    library/lib.cmx library/global.cmx plugins/ltac/tactic_option.cmi
plugins/ltac/tactic_option.cmi : vernac/vernacexpr.cmo \
    plugins/ltac/tacexpr.cmi engine/proofview.cmi lib/pp.cmi
plugins/ltac/tauto.cmo : lib/util.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi engine/proofview.cmi \
    lib/pp.cmi library/nametab.cmi kernel/names.cmi vernac/mltop.cmi \
    plugins/ltac/ltac_plugin.cmo pretyping/locusops.cmi pretyping/locus.cmo \
    lib/loc.cmi library/libnames.cmi clib/int.cmi tactics/hipattern.cmi \
    library/goptions.cmi library/global.cmi interp/genredexpr.cmo \
    pretyping/geninterp.cmi engine/eConstr.cmi kernel/declarations.cmo \
    kernel/constr.cmi lib/cAst.cmi plugins/ltac/tauto.cmi
plugins/ltac/tauto.cmx : lib/util.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx engine/proofview.cmx \
    lib/pp.cmx library/nametab.cmx kernel/names.cmx vernac/mltop.cmx \
    plugins/ltac/ltac_plugin.cmx pretyping/locusops.cmx pretyping/locus.cmx \
    lib/loc.cmx library/libnames.cmx clib/int.cmx tactics/hipattern.cmx \
    library/goptions.cmx library/global.cmx interp/genredexpr.cmx \
    pretyping/geninterp.cmx engine/eConstr.cmx kernel/declarations.cmx \
    kernel/constr.cmx lib/cAst.cmx plugins/ltac/tauto.cmi
plugins/ltac/tauto.cmi :
plugins/micromega/certificate.cmo : lib/util.cmi \
    plugins/micromega/sos_types.cmi proofs/proof.cmi \
    plugins/micromega/polynomial.cmi plugins/micromega/mutils.cmi \
    plugins/micromega/micromega.cmi plugins/micromega/mfourier.cmi \
    clib/int.cmi clib/cList.cmi lib/cErrors.cmi \
    plugins/micromega/certificate.cmi
plugins/micromega/certificate.cmx : lib/util.cmx \
    plugins/micromega/sos_types.cmx proofs/proof.cmx \
    plugins/micromega/polynomial.cmx plugins/micromega/mutils.cmx \
    plugins/micromega/micromega.cmx plugins/micromega/mfourier.cmx \
    clib/int.cmx clib/cList.cmx lib/cErrors.cmx \
    plugins/micromega/certificate.cmi
plugins/micromega/certificate.cmi : plugins/micromega/sos_types.cmi \
    plugins/micromega/micromega.cmi
plugins/micromega/coq_micromega.cmo : engine/univGen.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    lib/system.cmi plugins/micromega/sos_types.cmi kernel/sorts.cmi \
    pretyping/retyping.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    printing/printer.cmi lib/pp.cmi proofs/pfedit.cmi \
    plugins/micromega/persistent_cache.cmi kernel/names.cmi \
    engine/namegen.cmi plugins/micromega/mutils.cmi \
    plugins/micromega/micromega.cmi plugins/micromega/mfourier.cmi \
    clib/int.cmi library/goptions.cmi lib/feedback.cmi engine/evd.cmi \
    kernel/environ.cmi lib/envars.cmi engine/eConstr.cmi library/coqlib.cmi \
    config/coq_config.cmi kernel/constr.cmi plugins/micromega/certificate.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/micromega/coq_micromega.cmi
plugins/micromega/coq_micromega.cmx : engine/univGen.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    lib/system.cmx plugins/micromega/sos_types.cmx kernel/sorts.cmx \
    pretyping/retyping.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    printing/printer.cmx lib/pp.cmx proofs/pfedit.cmx \
    plugins/micromega/persistent_cache.cmx kernel/names.cmx \
    engine/namegen.cmx plugins/micromega/mutils.cmx \
    plugins/micromega/micromega.cmx plugins/micromega/mfourier.cmx \
    clib/int.cmx library/goptions.cmx lib/feedback.cmx engine/evd.cmx \
    kernel/environ.cmx lib/envars.cmx engine/eConstr.cmx library/coqlib.cmx \
    config/coq_config.cmx kernel/constr.cmx plugins/micromega/certificate.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/micromega/coq_micromega.cmi
plugins/micromega/coq_micromega.cmi : engine/proofview.cmi \
    plugins/micromega/micromega.cmi engine/eConstr.cmi
plugins/micromega/csdpcert.cmo : plugins/micromega/sos_types.cmi \
    plugins/micromega/sos_lib.cmi plugins/micromega/sos.cmi \
    plugins/micromega/mutils.cmi plugins/micromega/micromega.cmi \
    clib/cList.cmi plugins/micromega/csdpcert.cmi
plugins/micromega/csdpcert.cmx : plugins/micromega/sos_types.cmx \
    plugins/micromega/sos_lib.cmx plugins/micromega/sos.cmx \
    plugins/micromega/mutils.cmx plugins/micromega/micromega.cmx \
    clib/cList.cmx plugins/micromega/csdpcert.cmi
plugins/micromega/csdpcert.cmi :
plugins/micromega/g_micromega.cmo : tactics/tactics.cmi \
    plugins/ltac/tacinterp.cmi plugins/ltac/tacentries.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi vernac/mltop.cmi \
    plugins/ltac/ltac_plugin.cmo lib/genarg.cmi parsing/extend.cmo \
    plugins/micromega/coq_micromega.cmi plugins/micromega/g_micromega.cmi
plugins/micromega/g_micromega.cmx : tactics/tactics.cmx \
    plugins/ltac/tacinterp.cmx plugins/ltac/tacentries.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx vernac/mltop.cmx \
    plugins/ltac/ltac_plugin.cmx lib/genarg.cmx parsing/extend.cmx \
    plugins/micromega/coq_micromega.cmx plugins/micromega/g_micromega.cmi
plugins/micromega/g_micromega.cmi :
plugins/micromega/mfourier.cmo : lib/util.cmi \
    plugins/micromega/polynomial.cmi clib/option.cmi clib/int.cmi \
    clib/cMap.cmi lib/cErrors.cmi plugins/micromega/mfourier.cmi
plugins/micromega/mfourier.cmx : lib/util.cmx \
    plugins/micromega/polynomial.cmx clib/option.cmx clib/int.cmx \
    clib/cMap.cmx lib/cErrors.cmx plugins/micromega/mfourier.cmi
plugins/micromega/mfourier.cmi : lib/util.cmi \
    plugins/micromega/polynomial.cmi clib/cSig.cmi
plugins/micromega/micromega.cmo : plugins/micromega/micromega.cmi
plugins/micromega/micromega.cmx : plugins/micromega/micromega.cmi
plugins/micromega/micromega.cmi :
plugins/micromega/mutils.cmo : plugins/micromega/micromega.cmi clib/int.cmi \
    plugins/micromega/mutils.cmi
plugins/micromega/mutils.cmx : plugins/micromega/micromega.cmx clib/int.cmx \
    plugins/micromega/mutils.cmi
plugins/micromega/mutils.cmi : plugins/micromega/micromega.cmi clib/cSig.cmi
plugins/micromega/persistent_cache.cmo : lib/cErrors.cmi \
    plugins/micromega/persistent_cache.cmi
plugins/micromega/persistent_cache.cmx : lib/cErrors.cmx \
    plugins/micromega/persistent_cache.cmi
plugins/micromega/persistent_cache.cmi :
plugins/micromega/polynomial.cmo : plugins/micromega/mutils.cmi clib/int.cmi \
    plugins/micromega/polynomial.cmi
plugins/micromega/polynomial.cmx : plugins/micromega/mutils.cmx clib/int.cmx \
    plugins/micromega/polynomial.cmi
plugins/micromega/polynomial.cmi : clib/int.cmi
plugins/micromega/sos.cmo : plugins/micromega/sos_types.cmi \
    plugins/micromega/sos_lib.cmi plugins/micromega/sos.cmi
plugins/micromega/sos.cmx : plugins/micromega/sos_types.cmx \
    plugins/micromega/sos_lib.cmx plugins/micromega/sos.cmi
plugins/micromega/sos.cmi : plugins/micromega/sos_types.cmi
plugins/micromega/sos_lib.cmo : plugins/micromega/sos_lib.cmi
plugins/micromega/sos_lib.cmx : plugins/micromega/sos_lib.cmi
plugins/micromega/sos_lib.cmi :
plugins/micromega/sos_types.cmo : plugins/micromega/sos_types.cmi
plugins/micromega/sos_types.cmx : plugins/micromega/sos_types.cmi
plugins/micromega/sos_types.cmi :
plugins/nsatz/g_nsatz.cmo : plugins/ltac/tacentries.cmi interp/stdarg.cmi \
    plugins/nsatz/nsatz.cmi vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo \
    lib/genarg.cmi parsing/extend.cmo engine/eConstr.cmi
plugins/nsatz/g_nsatz.cmx : plugins/ltac/tacentries.cmx interp/stdarg.cmx \
    plugins/nsatz/nsatz.cmx vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx \
    lib/genarg.cmx parsing/extend.cmx engine/eConstr.cmx
plugins/nsatz/ideal.cmo : plugins/nsatz/utile.cmi lib/util.cmi \
    plugins/nsatz/polynom.cmi clib/int.cmi clib/heap.cmi clib/cList.cmi \
    plugins/nsatz/ideal.cmi
plugins/nsatz/ideal.cmx : plugins/nsatz/utile.cmx lib/util.cmx \
    plugins/nsatz/polynom.cmx clib/int.cmx clib/heap.cmx clib/cList.cmx \
    plugins/nsatz/ideal.cmi
plugins/nsatz/ideal.cmi : plugins/nsatz/polynom.cmi
plugins/nsatz/nsatz.cmo : plugins/nsatz/utile.cmi lib/util.cmi \
    engine/univGen.cmi tactics/tactics.cmi lib/pp.cmi \
    plugins/nsatz/polynom.cmi clib/int.cmi plugins/nsatz/ideal.cmi \
    engine/eConstr.cmi library/coqlib.cmi kernel/constr.cmi clib/cList.cmi \
    lib/cErrors.cmi plugins/nsatz/nsatz.cmi
plugins/nsatz/nsatz.cmx : plugins/nsatz/utile.cmx lib/util.cmx \
    engine/univGen.cmx tactics/tactics.cmx lib/pp.cmx \
    plugins/nsatz/polynom.cmx clib/int.cmx plugins/nsatz/ideal.cmx \
    engine/eConstr.cmx library/coqlib.cmx kernel/constr.cmx clib/cList.cmx \
    lib/cErrors.cmx plugins/nsatz/nsatz.cmi
plugins/nsatz/nsatz.cmi : engine/proofview.cmi kernel/constr.cmi
plugins/nsatz/polynom.cmo : plugins/nsatz/utile.cmi lib/util.cmi \
    clib/int.cmi plugins/nsatz/polynom.cmi
plugins/nsatz/polynom.cmx : plugins/nsatz/utile.cmx lib/util.cmx \
    clib/int.cmx plugins/nsatz/polynom.cmi
plugins/nsatz/polynom.cmi :
plugins/nsatz/utile.cmo : lib/pp.cmi lib/flags.cmi lib/feedback.cmi \
    lib/cErrors.cmi plugins/nsatz/utile.cmi
plugins/nsatz/utile.cmx : lib/pp.cmx lib/flags.cmx lib/feedback.cmx \
    lib/cErrors.cmx plugins/nsatz/utile.cmi
plugins/nsatz/utile.cmi :
plugins/omega/coq_omega.cmo : lib/util.cmi engine/univGen.cmi \
    engine/termops.cmi proofs/tactypes.cmo tactics/tactics.cmi \
    tactics/tacticals.cmi pretyping/tacred.cmi proofs/tacmach.cmi \
    proofs/refine.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    lib/pp.cmi plugins/omega/omega.cmo library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi proofs/logic.cmi pretyping/locus.cmo \
    library/libnames.cmi clib/int.cmi library/goptions.cmi \
    library/globnames.cmi library/global.cmi engine/evd.cmi \
    engine/evarutil.cmi tactics/equality.cmi engine/eConstr.cmi \
    library/coqlib.cmi tactics/contradiction.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi clib/bigint.cmi
plugins/omega/coq_omega.cmx : lib/util.cmx engine/univGen.cmx \
    engine/termops.cmx proofs/tactypes.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx pretyping/tacred.cmx proofs/tacmach.cmx \
    proofs/refine.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    lib/pp.cmx plugins/omega/omega.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx proofs/logic.cmx pretyping/locus.cmx \
    library/libnames.cmx clib/int.cmx library/goptions.cmx \
    library/globnames.cmx library/global.cmx engine/evd.cmx \
    engine/evarutil.cmx tactics/equality.cmx engine/eConstr.cmx \
    library/coqlib.cmx tactics/contradiction.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx clib/bigint.cmx
plugins/omega/g_omega.cmo : lib/util.cmi tactics/tacticals.cmi \
    plugins/ltac/tacinterp.cmi plugins/ltac/tacenv.cmi \
    plugins/ltac/tacentries.cmi interp/stdarg.cmi lib/pp.cmi kernel/names.cmi \
    vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo lib/genarg.cmi \
    parsing/extend.cmo plugins/omega/coq_omega.cmo lib/cErrors.cmi
plugins/omega/g_omega.cmx : lib/util.cmx tactics/tacticals.cmx \
    plugins/ltac/tacinterp.cmx plugins/ltac/tacenv.cmx \
    plugins/ltac/tacentries.cmx interp/stdarg.cmx lib/pp.cmx kernel/names.cmx \
    vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx lib/genarg.cmx \
    parsing/extend.cmx plugins/omega/coq_omega.cmx lib/cErrors.cmx
plugins/omega/omega.cmo : lib/util.cmi clib/int.cmi
plugins/omega/omega.cmx : lib/util.cmx clib/int.cmx
plugins/quote/g_quote.cmo : plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacentries.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi plugins/quote/quote.cmo \
    kernel/names.cmi vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo \
    pretyping/locus.cmo lib/loc.cmi pretyping/geninterp.cmi lib/genarg.cmi \
    parsing/extend.cmo engine/eConstr.cmi lib/cAst.cmi
plugins/quote/g_quote.cmx : plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacentries.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx plugins/quote/quote.cmx \
    kernel/names.cmx vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx \
    pretyping/locus.cmx lib/loc.cmx pretyping/geninterp.cmx lib/genarg.cmx \
    parsing/extend.cmx engine/eConstr.cmx lib/cAst.cmx
plugins/quote/quote.cmo : lib/util.cmi engine/univGen.cmi engine/termops.cmi \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi lib/pp.cmi \
    pretyping/patternops.cmi pretyping/pattern.cmo clib/option.cmi \
    kernel/names.cmi clib/int.cmi library/global.cmi kernel/environ.cmi \
    engine/eConstr.cmi library/coqlib.cmi pretyping/constr_matching.cmi \
    kernel/constr.cmi lib/cErrors.cmi
plugins/quote/quote.cmx : lib/util.cmx engine/univGen.cmx engine/termops.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx lib/pp.cmx \
    pretyping/patternops.cmx pretyping/pattern.cmx clib/option.cmx \
    kernel/names.cmx clib/int.cmx library/global.cmx kernel/environ.cmx \
    engine/eConstr.cmx library/coqlib.cmx pretyping/constr_matching.cmx \
    kernel/constr.cmx lib/cErrors.cmx
plugins/romega/const_omega.cmo : lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi proofs/tacmach.cmi pretyping/reductionops.cmi \
    engine/proofview.cmi clib/option.cmi library/nametab.cmi kernel/names.cmi \
    library/globnames.cmi library/global.cmi engine/evd.cmi \
    engine/eConstr.cmi library/coqlib.cmi kernel/constr.cmi clib/bigint.cmi \
    plugins/romega/const_omega.cmi
plugins/romega/const_omega.cmx : lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx proofs/tacmach.cmx pretyping/reductionops.cmx \
    engine/proofview.cmx clib/option.cmx library/nametab.cmx kernel/names.cmx \
    library/globnames.cmx library/global.cmx engine/evd.cmx \
    engine/eConstr.cmx library/coqlib.cmx kernel/constr.cmx clib/bigint.cmx \
    plugins/romega/const_omega.cmi
plugins/romega/const_omega.cmi : engine/proofview.cmi engine/evd.cmi \
    engine/eConstr.cmi clib/bigint.cmi
plugins/romega/g_romega.cmo : vernac/vernacinterp.cmi lib/util.cmi \
    tactics/tactics.cmi tactics/tacticals.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacenv.cmi plugins/ltac/tacentries.cmi interp/stdarg.cmi \
    plugins/romega/refl_omega.cmo engine/proofview.cmi lib/pp.cmi \
    kernel/names.cmi vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo \
    lib/genarg.cmi parsing/extend.cmo lib/cErrors.cmi
plugins/romega/g_romega.cmx : vernac/vernacinterp.cmx lib/util.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacenv.cmx plugins/ltac/tacentries.cmx interp/stdarg.cmx \
    plugins/romega/refl_omega.cmx engine/proofview.cmx lib/pp.cmx \
    kernel/names.cmx vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx \
    lib/genarg.cmx parsing/extend.cmx lib/cErrors.cmx
plugins/romega/refl_omega.cmo : lib/util.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi engine/proofview.cmi \
    printing/printer.cmi lib/pp.cmi proofs/pfedit.cmi \
    plugins/omega/omega_plugin.cmo kernel/names.cmi proofs/logic.cmi \
    clib/int.cmi lib/feedback.cmi engine/eConstr.cmi library/coqlib.cmi \
    kernel/context.cmi kernel/constr.cmi plugins/romega/const_omega.cmi \
    lib/cErrors.cmi clib/bigint.cmi
plugins/romega/refl_omega.cmx : lib/util.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx engine/proofview.cmx \
    printing/printer.cmx lib/pp.cmx proofs/pfedit.cmx \
    plugins/omega/omega_plugin.cmx kernel/names.cmx proofs/logic.cmx \
    clib/int.cmx lib/feedback.cmx engine/eConstr.cmx library/coqlib.cmx \
    kernel/context.cmx kernel/constr.cmx plugins/romega/const_omega.cmx \
    lib/cErrors.cmx clib/bigint.cmx
plugins/rtauto/g_rtauto.cmo : plugins/ltac/tacentries.cmi \
    plugins/rtauto/refl_tauto.cmi engine/proofview.cmi vernac/mltop.cmi \
    plugins/ltac/ltac_plugin.cmo
plugins/rtauto/g_rtauto.cmx : plugins/ltac/tacentries.cmx \
    plugins/rtauto/refl_tauto.cmx engine/proofview.cmx vernac/mltop.cmx \
    plugins/ltac/ltac_plugin.cmx
plugins/rtauto/proof_search.cmo : lib/util.cmi lib/pp.cmi clib/int.cmi \
    library/goptions.cmi lib/feedback.cmi lib/control.cmi lib/cErrors.cmi \
    plugins/rtauto/proof_search.cmi
plugins/rtauto/proof_search.cmx : lib/util.cmx lib/pp.cmx clib/int.cmx \
    library/goptions.cmx lib/feedback.cmx lib/control.cmx lib/cErrors.cmx \
    plugins/rtauto/proof_search.cmi
plugins/rtauto/proof_search.cmi : lib/pp.cmi
plugins/rtauto/refl_tauto.cmo : kernel/vars.cmi lib/util.cmi \
    engine/univGen.cmi engine/termops.cmi kernel/term.cmi tactics/tactics.cmi \
    plugins/ltac/tactic_debug.cmi proofs/tacmach.cmi \
    plugins/ltac/tacinterp.cmi lib/system.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi \
    plugins/rtauto/proof_search.cmi lib/pp.cmi kernel/names.cmi \
    plugins/ltac/ltac_plugin.cmo clib/int.cmi library/goptions.cmi \
    lib/feedback.cmi lib/explore.cmi engine/evd.cmi engine/eConstr.cmi \
    library/coqlib.cmi kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    kernel/cClosure.cmi plugins/rtauto/refl_tauto.cmi
plugins/rtauto/refl_tauto.cmx : kernel/vars.cmx lib/util.cmx \
    engine/univGen.cmx engine/termops.cmx kernel/term.cmx tactics/tactics.cmx \
    plugins/ltac/tactic_debug.cmx proofs/tacmach.cmx \
    plugins/ltac/tacinterp.cmx lib/system.cmx pretyping/retyping.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx \
    plugins/rtauto/proof_search.cmx lib/pp.cmx kernel/names.cmx \
    plugins/ltac/ltac_plugin.cmx clib/int.cmx library/goptions.cmx \
    lib/feedback.cmx lib/explore.cmx engine/evd.cmx engine/eConstr.cmx \
    library/coqlib.cmx kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    kernel/cClosure.cmx plugins/rtauto/refl_tauto.cmi
plugins/rtauto/refl_tauto.cmi : proofs/tacmach.cmi \
    plugins/rtauto/proof_search.cmi kernel/names.cmi proofs/goal.cmi \
    engine/evd.cmi engine/eConstr.cmi kernel/constr.cmi
plugins/setoid_ring/g_newring.cmo : vernac/vernacentries.cmi \
    stm/vernac_classifier.cmi lib/util.cmi plugins/ltac/tacentries.cmi \
    plugins/ltac/tacarg.cmi interp/stdarg.cmi printing/printer.cmi \
    plugins/ltac/pptactic.cmi printing/ppconstr.cmi lib/pp.cmi \
    plugins/ltac/pltac.cmi proofs/pfedit.cmi parsing/pcoq.cmi \
    plugins/setoid_ring/newring_ast.cmi plugins/setoid_ring/newring.cmi \
    vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo library/libnames.cmi \
    lib/genarg.cmi lib/feedback.cmi parsing/extend.cmo parsing/cLexer.cmi
plugins/setoid_ring/g_newring.cmx : vernac/vernacentries.cmx \
    stm/vernac_classifier.cmx lib/util.cmx plugins/ltac/tacentries.cmx \
    plugins/ltac/tacarg.cmx interp/stdarg.cmx printing/printer.cmx \
    plugins/ltac/pptactic.cmx printing/ppconstr.cmx lib/pp.cmx \
    plugins/ltac/pltac.cmx proofs/pfedit.cmx parsing/pcoq.cmx \
    plugins/setoid_ring/newring_ast.cmx plugins/setoid_ring/newring.cmx \
    vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx library/libnames.cmx \
    lib/genarg.cmx lib/feedback.cmx parsing/extend.cmx parsing/cLexer.cmx
plugins/setoid_ring/newring.cmo : kernel/vars.cmi lib/util.cmi \
    engine/univops.cmi engine/univGen.cmi pretyping/typing.cmi \
    engine/termops.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    plugins/ltac/tacsubst.cmi proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacenv.cmi library/summary.cmi interp/stdarg.cmi \
    interp/smartlocate.cmi plugins/ltac/rewrite.cmi pretyping/retyping.cmi \
    proofs/refiner.cmi pretyping/reductionops.cmi proofs/redexpr.cmi \
    engine/proofview.cmi printing/printer.cmi lib/pp.cmi clib/option.cmi \
    plugins/setoid_ring/newring_ast.cmi kernel/names.cmi kernel/mod_subst.cmi \
    plugins/ltac/ltac_plugin.cmo pretyping/locus.cmo lib/loc.cmi \
    library/libobject.cmi library/libnames.cmi library/lib.cmi clib/int.cmi \
    proofs/goal.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo lib/genarg.cmi lib/flags.cmi lib/feedback.cmi \
    engine/evd.cmi engine/evarutil.cmi kernel/esubst.cmi kernel/environ.cmi \
    kernel/entries.cmo engine/eConstr.cmi interp/declare.cmi \
    library/decl_kinds.cmo lib/dAst.cmi library/coqlib.cmi \
    interp/constrintern.cmi kernel/constr.cmi lib/cErrors.cmi \
    kernel/cClosure.cmi lib/cAst.cmi plugins/setoid_ring/newring.cmi
plugins/setoid_ring/newring.cmx : kernel/vars.cmx lib/util.cmx \
    engine/univops.cmx engine/univGen.cmx pretyping/typing.cmx \
    engine/termops.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    plugins/ltac/tacsubst.cmx proofs/tacmach.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacenv.cmx library/summary.cmx interp/stdarg.cmx \
    interp/smartlocate.cmx plugins/ltac/rewrite.cmx pretyping/retyping.cmx \
    proofs/refiner.cmx pretyping/reductionops.cmx proofs/redexpr.cmx \
    engine/proofview.cmx printing/printer.cmx lib/pp.cmx clib/option.cmx \
    plugins/setoid_ring/newring_ast.cmx kernel/names.cmx kernel/mod_subst.cmx \
    plugins/ltac/ltac_plugin.cmx pretyping/locus.cmx lib/loc.cmx \
    library/libobject.cmx library/libnames.cmx library/lib.cmx clib/int.cmx \
    proofs/goal.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx lib/genarg.cmx lib/flags.cmx lib/feedback.cmx \
    engine/evd.cmx engine/evarutil.cmx kernel/esubst.cmx kernel/environ.cmx \
    kernel/entries.cmx engine/eConstr.cmx interp/declare.cmx \
    library/decl_kinds.cmx lib/dAst.cmx library/coqlib.cmx \
    interp/constrintern.cmx kernel/constr.cmx lib/cErrors.cmx \
    kernel/cClosure.cmx lib/cAst.cmx plugins/setoid_ring/newring.cmi
plugins/setoid_ring/newring.cmi : engine/proofview.cmi \
    plugins/setoid_ring/newring_ast.cmi kernel/names.cmi library/libnames.cmi \
    pretyping/geninterp.cmi engine/eConstr.cmi interp/constrexpr.cmo
plugins/setoid_ring/newring_ast.cmo : plugins/ltac/tacexpr.cmi \
    plugins/ltac/ltac_plugin.cmo library/libnames.cmi interp/constrexpr.cmo \
    kernel/constr.cmi plugins/setoid_ring/newring_ast.cmi
plugins/setoid_ring/newring_ast.cmx : plugins/ltac/tacexpr.cmx \
    plugins/ltac/ltac_plugin.cmx library/libnames.cmx interp/constrexpr.cmx \
    kernel/constr.cmx plugins/setoid_ring/newring_ast.cmi
plugins/setoid_ring/newring_ast.cmi : plugins/ltac/tacexpr.cmi \
    plugins/ltac/ltac_plugin.cmo library/libnames.cmi interp/constrexpr.cmo \
    kernel/constr.cmi
plugins/ssr/ssrast.cmi : proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi engine/proofview.cmi kernel/names.cmi \
    plugins/ltac/ltac_plugin.cmo pretyping/locus.cmo lib/loc.cmi \
    proofs/goal.cmi pretyping/geninterp.cmi interp/genintern.cmi \
    engine/evd.cmi interp/constrexpr.cmo
plugins/ssr/ssrbwd.cmo : tactics/tacticals.cmi proofs/tacmach.cmi \
    plugins/ssr/ssrview.cmi plugins/ssr/ssrprinters.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrcommon.cmi \
    plugins/ssr/ssrast.cmi engine/proofview.cmi printing/printer.cmi \
    pretyping/pretyping.cmi lib/pp.cmi lib/loc.cmi library/globnames.cmi \
    pretyping/glob_term.cmo engine/eConstr.cmi lib/dAst.cmi lib/cAst.cmi \
    plugins/ssr/ssrbwd.cmi
plugins/ssr/ssrbwd.cmx : tactics/tacticals.cmx proofs/tacmach.cmx \
    plugins/ssr/ssrview.cmx plugins/ssr/ssrprinters.cmx \
    plugins/ssrmatching/ssrmatching_plugin.cmx \
    plugins/ssrmatching/ssrmatching.cmx plugins/ssr/ssrcommon.cmx \
    plugins/ssr/ssrast.cmi engine/proofview.cmx printing/printer.cmx \
    pretyping/pretyping.cmx lib/pp.cmx lib/loc.cmx library/globnames.cmx \
    pretyping/glob_term.cmx engine/eConstr.cmx lib/dAst.cmx lib/cAst.cmx \
    plugins/ssr/ssrbwd.cmi
plugins/ssr/ssrbwd.cmi : plugins/ssr/ssrast.cmi engine/proofview.cmi
plugins/ssr/ssrcommon.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    engine/uState.cmi pretyping/typing.cmi pretyping/typeclasses.cmi \
    engine/termops.cmi kernel/term.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi pretyping/tacred.cmi \
    proofs/tacmach.cmi plugins/ltac/tacinterp.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacenv.cmi interp/stdarg.cmi plugins/ssr/ssrprinters.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrast.cmi \
    interp/smartlocate.cmi pretyping/retyping.cmi proofs/refiner.cmi \
    proofs/refine.cmi pretyping/reductionops.cmi proofs/redexpr.cmi \
    engine/proofview_monad.cmi engine/proofview.cmi printing/printer.cmi \
    pretyping/pretyping.cmi lib/pp.cmi clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/namegen.cmi kernel/mod_subst.cmi \
    pretyping/ltac_pretype.cmo plugins/ltac/ltac_plugin.cmo \
    pretyping/locusops.cmi pretyping/locus.cmo lib/loc.cmi \
    library/libnames.cmi library/goptions.cmi proofs/goal.cmi \
    library/globnames.cmi pretyping/glob_term.cmo pretyping/glob_ops.cmi \
    interp/genredexpr.cmo pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi engine/ftactic.cmi engine/evd.cmi engine/evarutil.cmi \
    engine/evar_kinds.cmi kernel/evar.cmi tactics/equality.cmi \
    kernel/environ.cmi engine/eConstr.cmi library/decl_kinds.cmo lib/dAst.cmi \
    library/coqlib.cmi kernel/context.cmi interp/constrintern.cmi \
    interp/constrexpr.cmo kernel/constr.cmi clib/cString.cmi clib/cList.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi kernel/cClosure.cmi lib/cAst.cmi \
    plugins/ssr/ssrcommon.cmi
plugins/ssr/ssrcommon.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    engine/uState.cmx pretyping/typing.cmx pretyping/typeclasses.cmx \
    engine/termops.cmx kernel/term.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx pretyping/tacred.cmx \
    proofs/tacmach.cmx plugins/ltac/tacinterp.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacenv.cmx interp/stdarg.cmx plugins/ssr/ssrprinters.cmx \
    plugins/ssrmatching/ssrmatching_plugin.cmx \
    plugins/ssrmatching/ssrmatching.cmx plugins/ssr/ssrast.cmi \
    interp/smartlocate.cmx pretyping/retyping.cmx proofs/refiner.cmx \
    proofs/refine.cmx pretyping/reductionops.cmx proofs/redexpr.cmx \
    engine/proofview_monad.cmx engine/proofview.cmx printing/printer.cmx \
    pretyping/pretyping.cmx lib/pp.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/namegen.cmx kernel/mod_subst.cmx \
    pretyping/ltac_pretype.cmx plugins/ltac/ltac_plugin.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx lib/loc.cmx \
    library/libnames.cmx library/goptions.cmx proofs/goal.cmx \
    library/globnames.cmx pretyping/glob_term.cmx pretyping/glob_ops.cmx \
    interp/genredexpr.cmx pretyping/geninterp.cmx interp/genintern.cmx \
    lib/genarg.cmx engine/ftactic.cmx engine/evd.cmx engine/evarutil.cmx \
    engine/evar_kinds.cmx kernel/evar.cmx tactics/equality.cmx \
    kernel/environ.cmx engine/eConstr.cmx library/decl_kinds.cmx lib/dAst.cmx \
    library/coqlib.cmx kernel/context.cmx interp/constrintern.cmx \
    interp/constrexpr.cmx kernel/constr.cmx clib/cString.cmx clib/cList.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx kernel/cClosure.cmx lib/cAst.cmx \
    plugins/ssr/ssrcommon.cmi
plugins/ssr/ssrcommon.cmi : engine/uState.cmi proofs/tacmach.cmi \
    plugins/ltac/tacinterp.cmi plugins/ltac/tacexpr.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrast.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi proofs/proof_type.cmo \
    lib/pp.cmi kernel/names.cmi kernel/mod_subst.cmi \
    plugins/ltac/ltac_plugin.cmo lib/loc.cmi library/libnames.cmi \
    proofs/goal.cmi pretyping/glob_term.cmo pretyping/geninterp.cmi \
    interp/genintern.cmi lib/genarg.cmi engine/evd.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    interp/constrexpr.cmo kernel/constr.cmi
plugins/ssr/ssrelim.cmo : lib/util.cmi engine/termops.cmi kernel/term.cmi \
    proofs/tactypes.cmo tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi plugins/ssr/ssrprinters.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrcommon.cmi \
    plugins/ssr/ssrast.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    printing/printer.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    kernel/inductive.cmi pretyping/indrec.cmi library/globnames.cmi \
    lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi kernel/evar.cmi \
    tactics/equality.cmi engine/eConstr.cmi kernel/declarations.cmo \
    library/coqlib.cmi kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    plugins/ssr/ssrelim.cmi
plugins/ssr/ssrelim.cmx : lib/util.cmx engine/termops.cmx kernel/term.cmx \
    proofs/tactypes.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx plugins/ssr/ssrprinters.cmx \
    plugins/ssrmatching/ssrmatching_plugin.cmx \
    plugins/ssrmatching/ssrmatching.cmx plugins/ssr/ssrcommon.cmx \
    plugins/ssr/ssrast.cmi pretyping/reductionops.cmx engine/proofview.cmx \
    printing/printer.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    kernel/inductive.cmx pretyping/indrec.cmx library/globnames.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx kernel/evar.cmx \
    tactics/equality.cmx engine/eConstr.cmx kernel/declarations.cmx \
    library/coqlib.cmx kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    plugins/ssr/ssrelim.cmi
plugins/ssr/ssrelim.cmi : proofs/tacmach.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrast.cmi \
    engine/proofview.cmi proofs/goal.cmi engine/evd.cmi engine/eConstr.cmi
plugins/ssr/ssrequality.cmo : kernel/vars.cmi lib/util.cmi \
    engine/univGen.cmi engine/uState.cmi pretyping/typing.cmi \
    engine/termops.cmi kernel/term.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi pretyping/tacred.cmi proofs/tacmach.cmi \
    plugins/ltac/tacinterp.cmi library/summary.cmi \
    plugins/ssr/ssrprinters.cmi plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrelim.cmi \
    plugins/ssr/ssrcommon.cmi plugins/ssr/ssrast.cmi kernel/sorts.cmi \
    plugins/ltac/rewrite.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi interp/redops.cmi proofs/redexpr.cmi \
    engine/proofview.cmi printing/printer.cmi lib/pp.cmi clib/option.cmi \
    kernel/names.cmi engine/nameops.cmi plugins/ltac/ltac_plugin.cmo \
    proofs/logic.cmi pretyping/locus.cmo pretyping/inductiveops.cmi \
    pretyping/indrec.cmi tactics/hipattern.cmi vernac/himsg.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    interp/genredexpr.cmo lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi \
    pretyping/detyping.cmi library/coqlib.cmi kernel/constr.cmi \
    lib/cErrors.cmi kernel/cClosure.cmi plugins/ssr/ssrequality.cmi
plugins/ssr/ssrequality.cmx : kernel/vars.cmx lib/util.cmx \
    engine/univGen.cmx engine/uState.cmx pretyping/typing.cmx \
    engine/termops.cmx kernel/term.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx pretyping/tacred.cmx proofs/tacmach.cmx \
    plugins/ltac/tacinterp.cmx library/summary.cmx \
    plugins/ssr/ssrprinters.cmx plugins/ssrmatching/ssrmatching_plugin.cmx \
    plugins/ssrmatching/ssrmatching.cmx plugins/ssr/ssrelim.cmx \
    plugins/ssr/ssrcommon.cmx plugins/ssr/ssrast.cmi kernel/sorts.cmx \
    plugins/ltac/rewrite.cmx pretyping/retyping.cmx \
    pretyping/reductionops.cmx interp/redops.cmx proofs/redexpr.cmx \
    engine/proofview.cmx printing/printer.cmx lib/pp.cmx clib/option.cmx \
    kernel/names.cmx engine/nameops.cmx plugins/ltac/ltac_plugin.cmx \
    proofs/logic.cmx pretyping/locus.cmx pretyping/inductiveops.cmx \
    pretyping/indrec.cmx tactics/hipattern.cmx vernac/himsg.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    interp/genredexpr.cmx lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx \
    kernel/evar.cmx kernel/environ.cmx engine/eConstr.cmx \
    pretyping/detyping.cmx library/coqlib.cmx kernel/constr.cmx \
    lib/cErrors.cmx kernel/cClosure.cmx plugins/ssr/ssrequality.cmi
plugins/ssr/ssrequality.cmi : proofs/tacmach.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrast.cmi \
    plugins/ltac/ltac_plugin.cmo proofs/goal.cmi engine/evd.cmi \
    engine/eConstr.cmi
plugins/ssr/ssrfwd.cmo : lib/util.cmi engine/termops.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi library/summary.cmi \
    plugins/ssr/ssrtacticals.cmi plugins/ssr/ssrprinters.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo plugins/ssr/ssripats.cmi \
    plugins/ssr/ssrcommon.cmi plugins/ssr/ssrast.cmi engine/proofview.cmi \
    printing/printer.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    pretyping/locusops.cmi library/goptions.cmi pretyping/glob_term.cmo \
    engine/evd.cmi engine/evarutil.cmi engine/eConstr.cmi lib/dAst.cmi \
    kernel/context.cmi interp/constrexpr.cmo kernel/constr.cmi \
    lib/cErrors.cmi lib/cAst.cmi plugins/ssr/ssrfwd.cmi
plugins/ssr/ssrfwd.cmx : lib/util.cmx engine/termops.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx library/summary.cmx \
    plugins/ssr/ssrtacticals.cmx plugins/ssr/ssrprinters.cmx \
    plugins/ssrmatching/ssrmatching_plugin.cmx plugins/ssr/ssripats.cmx \
    plugins/ssr/ssrcommon.cmx plugins/ssr/ssrast.cmi engine/proofview.cmx \
    printing/printer.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    pretyping/locusops.cmx library/goptions.cmx pretyping/glob_term.cmx \
    engine/evd.cmx engine/evarutil.cmx engine/eConstr.cmx lib/dAst.cmx \
    kernel/context.cmx interp/constrexpr.cmx kernel/constr.cmx \
    lib/cErrors.cmx lib/cAst.cmx plugins/ssr/ssrfwd.cmi
plugins/ssr/ssrfwd.cmi : proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo plugins/ssr/ssrast.cmi \
    kernel/names.cmi plugins/ltac/ltac_plugin.cmo proofs/goal.cmi \
    engine/evd.cmi kernel/evar.cmi engine/eConstr.cmi
plugins/ssr/ssripats.cmo : kernel/vars.cmi lib/util.cmi pretyping/typing.cmi \
    engine/termops.cmi kernel/term.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi library/summary.cmi \
    plugins/ssr/ssrview.cmi plugins/ssr/ssrprinters.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrequality.cmi \
    plugins/ssr/ssrelim.cmi plugins/ssr/ssrcommon.cmi plugins/ssr/ssrast.cmi \
    engine/proofview_monad.cmi engine/proofview.cmi printing/printer.cmi \
    lib/pp.cmi clib/option.cmi kernel/names.cmi proofs/goal.cmi \
    engine/evd.cmi engine/evarutil.cmi engine/eConstr.cmi library/coqlib.cmi \
    kernel/context.cmi kernel/constr.cmi clib/cList.cmi \
    plugins/ssr/ssripats.cmi
plugins/ssr/ssripats.cmx : kernel/vars.cmx lib/util.cmx pretyping/typing.cmx \
    engine/termops.cmx kernel/term.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx library/summary.cmx \
    plugins/ssr/ssrview.cmx plugins/ssr/ssrprinters.cmx \
    plugins/ssrmatching/ssrmatching_plugin.cmx \
    plugins/ssrmatching/ssrmatching.cmx plugins/ssr/ssrequality.cmx \
    plugins/ssr/ssrelim.cmx plugins/ssr/ssrcommon.cmx plugins/ssr/ssrast.cmi \
    engine/proofview_monad.cmx engine/proofview.cmx printing/printer.cmx \
    lib/pp.cmx clib/option.cmx kernel/names.cmx proofs/goal.cmx \
    engine/evd.cmx engine/evarutil.cmx engine/eConstr.cmx library/coqlib.cmx \
    kernel/context.cmx kernel/constr.cmx clib/cList.cmx \
    plugins/ssr/ssripats.cmi
plugins/ssr/ssripats.cmi : plugins/ssr/ssrast.cmi engine/proofview.cmi \
    proofs/goal.cmi engine/evd.cmi kernel/evar.cmi engine/eConstr.cmi \
    kernel/constr.cmi
plugins/ssr/ssrparser.cmo : lib/util.cmi parsing/tok.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi plugins/ltac/tacsubst.cmi \
    proofs/tacmach.cmi plugins/ltac/tacinterp.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi \
    plugins/ltac/tacentries.cmi plugins/ltac/tacarg.cmi library/summary.cmi \
    interp/stdarg.cmi plugins/ssr/ssrtacticals.cmi \
    plugins/ssr/ssrprinters.cmi plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssr/ssripats.cmi plugins/ssr/ssrfwd.cmi \
    plugins/ssr/ssrequality.cmi plugins/ssr/ssrcommon.cmi \
    plugins/ssr/ssrbwd.cmi plugins/ssr/ssrast.cmi engine/proofview.cmi \
    plugins/ltac/pptactic.cmi printing/ppconstr.cmi lib/pp.cmi \
    plugins/ltac/pltac.cmi parsing/pcoq.cmi clib/option.cmi \
    parsing/notation_gram.cmo interp/notation.cmi kernel/names.cmi \
    engine/namegen.cmi vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo \
    pretyping/locus.cmo lib/loc.cmi library/libnames.cmi library/goptions.cmi \
    proofs/goal.cmi pretyping/glob_term.cmo pretyping/geninterp.cmi \
    interp/genintern.cmi lib/genarg.cmi engine/ftactic.cmi lib/feedback.cmi \
    plugins/ltac/extraargs.cmi parsing/extend.cmo engine/eConstr.cmi \
    pretyping/detyping.cmi library/decl_kinds.cmo interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo kernel/constr.cmi parsing/cLexer.cmi \
    lib/cErrors.cmi lib/cAst.cmi tactics/auto.cmi plugins/ssr/ssrparser.cmi
plugins/ssr/ssrparser.cmx : lib/util.cmx parsing/tok.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx plugins/ltac/tacsubst.cmx \
    proofs/tacmach.cmx plugins/ltac/tacinterp.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx \
    plugins/ltac/tacentries.cmx plugins/ltac/tacarg.cmx library/summary.cmx \
    interp/stdarg.cmx plugins/ssr/ssrtacticals.cmx \
    plugins/ssr/ssrprinters.cmx plugins/ssrmatching/ssrmatching_plugin.cmx \
    plugins/ssr/ssripats.cmx plugins/ssr/ssrfwd.cmx \
    plugins/ssr/ssrequality.cmx plugins/ssr/ssrcommon.cmx \
    plugins/ssr/ssrbwd.cmx plugins/ssr/ssrast.cmi engine/proofview.cmx \
    plugins/ltac/pptactic.cmx printing/ppconstr.cmx lib/pp.cmx \
    plugins/ltac/pltac.cmx parsing/pcoq.cmx clib/option.cmx \
    parsing/notation_gram.cmx interp/notation.cmx kernel/names.cmx \
    engine/namegen.cmx vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx \
    pretyping/locus.cmx lib/loc.cmx library/libnames.cmx library/goptions.cmx \
    proofs/goal.cmx pretyping/glob_term.cmx pretyping/geninterp.cmx \
    interp/genintern.cmx lib/genarg.cmx engine/ftactic.cmx lib/feedback.cmx \
    plugins/ltac/extraargs.cmx parsing/extend.cmx engine/eConstr.cmx \
    pretyping/detyping.cmx library/decl_kinds.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx kernel/constr.cmx parsing/cLexer.cmx \
    lib/cErrors.cmx lib/cAst.cmx tactics/auto.cmx plugins/ssr/ssrparser.cmi
plugins/ssr/ssrparser.cmi : plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacexpr.cmi plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrequality.cmi \
    plugins/ssr/ssrast.cmi lib/pp.cmi parsing/pcoq.cmi \
    parsing/notation_gram.cmo plugins/ltac/ltac_plugin.cmo \
    pretyping/geninterp.cmi lib/genarg.cmi
plugins/ssr/ssrprinters.cmo : proofs/tacmach.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrast.cmi \
    pretyping/reductionops.cmi printing/printer.cmi printing/ppconstr.cmi \
    lib/pp.cmi kernel/names.cmi library/goptions.cmi library/global.cmi \
    lib/feedback.cmi plugins/ssr/ssrprinters.cmi
plugins/ssr/ssrprinters.cmx : proofs/tacmach.cmx \
    plugins/ssrmatching/ssrmatching_plugin.cmx \
    plugins/ssrmatching/ssrmatching.cmx plugins/ssr/ssrast.cmi \
    pretyping/reductionops.cmx printing/printer.cmx printing/ppconstr.cmx \
    lib/pp.cmx kernel/names.cmx library/goptions.cmx library/global.cmx \
    lib/feedback.cmx plugins/ssr/ssrprinters.cmi
plugins/ssr/ssrprinters.cmi : plugins/ssr/ssrast.cmi lib/pp.cmi \
    proofs/goal.cmi pretyping/glob_term.cmo engine/evd.cmi engine/eConstr.cmi \
    interp/constrexpr.cmo
plugins/ssr/ssrtacticals.cmo : engine/termops.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi plugins/ssr/ssrcommon.cmi \
    plugins/ssr/ssrast.cmi engine/proofview.cmi lib/pp.cmi kernel/names.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo engine/evd.cmi \
    engine/eConstr.cmi kernel/context.cmi kernel/constr.cmi clib/cList.cmi \
    lib/cErrors.cmi plugins/ssr/ssrtacticals.cmi
plugins/ssr/ssrtacticals.cmx : engine/termops.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx plugins/ssr/ssrcommon.cmx \
    plugins/ssr/ssrast.cmi engine/proofview.cmx lib/pp.cmx kernel/names.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx engine/evd.cmx \
    engine/eConstr.cmx kernel/context.cmx kernel/constr.cmx clib/cList.cmx \
    lib/cErrors.cmx plugins/ssr/ssrtacticals.cmi
plugins/ssr/ssrtacticals.cmi : proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ssrmatching/ssrmatching_plugin.cmo \
    plugins/ssrmatching/ssrmatching.cmi plugins/ssr/ssrast.cmi \
    engine/proofview.cmi plugins/ltac/ltac_plugin.cmo pretyping/locus.cmo \
    proofs/goal.cmi engine/evd.cmi
plugins/ssr/ssrvernac.cmo : vernac/vernacinterp.cmi vernac/vernacexpr.cmo \
    vernac/vernacentries.cmi stm/vernac_classifier.cmi lib/util.cmi \
    engine/termops.cmi plugins/ltac/tacsubst.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacentries.cmi interp/stdarg.cmi plugins/ssr/ssrview.cmi \
    plugins/ssr/ssrprinters.cmi plugins/ssr/ssrparser.cmi \
    plugins/ssr/ssrcommon.cmi interp/smartlocate.cmi vernac/search.cmi \
    pretyping/reductionops.cmi vernac/pvernac.cmi printing/printer.cmi \
    plugins/ltac/pptactic.cmi printing/ppconstr.cmi lib/pp.cmi \
    plugins/ltac/pltac.cmi proofs/pfedit.cmi parsing/pcoq.cmi \
    pretyping/patternops.cmi pretyping/pattern.cmo clib/option.cmi \
    interp/notation_term.cmo interp/notation_ops.cmi interp/notation.cmi \
    library/nametab.cmi kernel/names.cmi vernac/mltop.cmi \
    plugins/ltac/ltac_plugin.cmo pretyping/locus.cmo vernac/locality.cmi \
    lib/loc.cmi interp/impargs.cmi library/global.cmi pretyping/glob_term.cmo \
    interp/genredexpr.cmo pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi vernac/g_vernac.cmo engine/ftactic.cmi lib/feedback.cmi \
    plugins/ltac/extraargs.cmi parsing/extend.cmo vernac/explainErr.cmi \
    engine/evd.cmi engine/evar_kinds.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo lib/dAst.cmi interp/constrintern.cmi \
    interp/constrextern.cmi interp/constrexpr_ops.cmi interp/constrexpr.cmo \
    pretyping/constr_matching.cmi kernel/constr.cmi pretyping/classops.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi plugins/ssr/ssrvernac.cmi
plugins/ssr/ssrvernac.cmx : vernac/vernacinterp.cmx vernac/vernacexpr.cmx \
    vernac/vernacentries.cmx stm/vernac_classifier.cmx lib/util.cmx \
    engine/termops.cmx plugins/ltac/tacsubst.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacentries.cmx interp/stdarg.cmx plugins/ssr/ssrview.cmx \
    plugins/ssr/ssrprinters.cmx plugins/ssr/ssrparser.cmx \
    plugins/ssr/ssrcommon.cmx interp/smartlocate.cmx vernac/search.cmx \
    pretyping/reductionops.cmx vernac/pvernac.cmx printing/printer.cmx \
    plugins/ltac/pptactic.cmx printing/ppconstr.cmx lib/pp.cmx \
    plugins/ltac/pltac.cmx proofs/pfedit.cmx parsing/pcoq.cmx \
    pretyping/patternops.cmx pretyping/pattern.cmx clib/option.cmx \
    interp/notation_term.cmx interp/notation_ops.cmx interp/notation.cmx \
    library/nametab.cmx kernel/names.cmx vernac/mltop.cmx \
    plugins/ltac/ltac_plugin.cmx pretyping/locus.cmx vernac/locality.cmx \
    lib/loc.cmx interp/impargs.cmx library/global.cmx pretyping/glob_term.cmx \
    interp/genredexpr.cmx pretyping/geninterp.cmx interp/genintern.cmx \
    lib/genarg.cmx vernac/g_vernac.cmx engine/ftactic.cmx lib/feedback.cmx \
    plugins/ltac/extraargs.cmx parsing/extend.cmx vernac/explainErr.cmx \
    engine/evd.cmx engine/evar_kinds.cmx engine/eConstr.cmx \
    library/decl_kinds.cmx lib/dAst.cmx interp/constrintern.cmx \
    interp/constrextern.cmx interp/constrexpr_ops.cmx interp/constrexpr.cmx \
    pretyping/constr_matching.cmx kernel/constr.cmx pretyping/classops.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx plugins/ssr/ssrvernac.cmi
plugins/ssr/ssrvernac.cmi :
plugins/ssr/ssrview.cmo : lib/util.cmi pretyping/typeclasses.cmi \
    kernel/term.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi plugins/ltac/tacinterp.cmi plugins/ltac/taccoerce.cmi \
    plugins/ltac/tacarg.cmi library/summary.cmi plugins/ssr/ssrprinters.cmi \
    plugins/ssr/ssrcommon.cmi plugins/ssr/ssrast.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi printing/printer.cmi \
    pretyping/pretyping.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/namegen.cmi plugins/ltac/ltac_plugin.cmo library/libobject.cmi \
    library/lib.cmi proofs/goal.cmi pretyping/glob_term.cmo \
    pretyping/glob_ops.cmi pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi engine/evd.cmi engine/evarutil.cmi engine/evar_kinds.cmi \
    kernel/evar.cmi engine/eConstr.cmi pretyping/detyping.cmi lib/dAst.cmi \
    kernel/context.cmi interp/constrintern.cmi kernel/constr.cmi \
    plugins/ssr/ssrview.cmi
plugins/ssr/ssrview.cmx : lib/util.cmx pretyping/typeclasses.cmx \
    kernel/term.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx plugins/ltac/tacinterp.cmx plugins/ltac/taccoerce.cmx \
    plugins/ltac/tacarg.cmx library/summary.cmx plugins/ssr/ssrprinters.cmx \
    plugins/ssr/ssrcommon.cmx plugins/ssr/ssrast.cmi pretyping/retyping.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx printing/printer.cmx \
    pretyping/pretyping.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/namegen.cmx plugins/ltac/ltac_plugin.cmx library/libobject.cmx \
    library/lib.cmx proofs/goal.cmx pretyping/glob_term.cmx \
    pretyping/glob_ops.cmx pretyping/geninterp.cmx interp/genintern.cmx \
    lib/genarg.cmx engine/evd.cmx engine/evarutil.cmx engine/evar_kinds.cmx \
    kernel/evar.cmx engine/eConstr.cmx pretyping/detyping.cmx lib/dAst.cmx \
    kernel/context.cmx interp/constrintern.cmx kernel/constr.cmx \
    plugins/ssr/ssrview.cmi
plugins/ssr/ssrview.cmi : plugins/ssr/ssrast.cmi engine/proofview.cmi \
    kernel/names.cmi pretyping/glob_term.cmo engine/eConstr.cmi
plugins/ssrmatching/g_ssrmatching.cmo : lib/util.cmi parsing/tok.cmi \
    plugins/ltac/tacsubst.cmi proofs/tacmach.cmi plugins/ltac/tacinterp.cmi \
    plugins/ltac/tacintern.cmi plugins/ltac/tacexpr.cmi \
    plugins/ltac/tacentries.cmi plugins/ssrmatching/ssrmatching.cmi \
    engine/proofview.cmi plugins/ltac/pptactic.cmi parsing/pcoq.cmi \
    vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo pretyping/geninterp.cmi \
    interp/genintern.cmi lib/genarg.cmi engine/ftactic.cmi parsing/extend.cmo \
    parsing/cLexer.cmi plugins/ssrmatching/g_ssrmatching.cmi
plugins/ssrmatching/g_ssrmatching.cmx : lib/util.cmx parsing/tok.cmx \
    plugins/ltac/tacsubst.cmx proofs/tacmach.cmx plugins/ltac/tacinterp.cmx \
    plugins/ltac/tacintern.cmx plugins/ltac/tacexpr.cmx \
    plugins/ltac/tacentries.cmx plugins/ssrmatching/ssrmatching.cmx \
    engine/proofview.cmx plugins/ltac/pptactic.cmx parsing/pcoq.cmx \
    vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx pretyping/geninterp.cmx \
    interp/genintern.cmx lib/genarg.cmx engine/ftactic.cmx parsing/extend.cmx \
    parsing/cLexer.cmx plugins/ssrmatching/g_ssrmatching.cmi
plugins/ssrmatching/g_ssrmatching.cmi : plugins/ssrmatching/ssrmatching.cmi \
    parsing/pcoq.cmi lib/genarg.cmi
plugins/ssrmatching/ssrmatching.cmo : kernel/vars.cmi lib/util.cmi \
    pretyping/unification.cmi engine/uState.cmi pretyping/typeclasses.cmi \
    engine/termops.cmi kernel/term.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi plugins/ltac/tacsubst.cmi proofs/tacmach.cmi \
    plugins/ltac/tacinterp.cmi plugins/ltac/tacintern.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacenv.cmi interp/stdarg.cmi \
    kernel/sorts.cmi pretyping/reductionops.cmi kernel/reduction.cmi \
    pretyping/recordops.cmi engine/proofview.cmi printing/printer.cmi \
    pretyping/pretyping.cmi pretyping/pretype_errors.cmi \
    plugins/ltac/pptactic.cmi printing/ppconstr.cmi lib/pp.cmi \
    proofs/pfedit.cmi clib/option.cmi kernel/names.cmi engine/namegen.cmi \
    vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo lib/loc.cmi \
    library/libnames.cmi library/goptions.cmi proofs/goal.cmi \
    library/globnames.cmi library/global.cmi pretyping/glob_term.cmo \
    pretyping/glob_ops.cmi pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi engine/ftactic.cmi lib/feedback.cmi engine/evd.cmi \
    engine/evarutil.cmi pretyping/evarconv.cmi engine/evar_kinds.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo lib/dAst.cmi kernel/conv_oracle.cmi \
    kernel/context.cmi interp/constrintern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo kernel/constr.cmi lib/cErrors.cmi lib/cAst.cmi \
    clib/cArray.cmi plugins/ssrmatching/ssrmatching.cmi
plugins/ssrmatching/ssrmatching.cmx : kernel/vars.cmx lib/util.cmx \
    pretyping/unification.cmx engine/uState.cmx pretyping/typeclasses.cmx \
    engine/termops.cmx kernel/term.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx plugins/ltac/tacsubst.cmx proofs/tacmach.cmx \
    plugins/ltac/tacinterp.cmx plugins/ltac/tacintern.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacenv.cmx interp/stdarg.cmx \
    kernel/sorts.cmx pretyping/reductionops.cmx kernel/reduction.cmx \
    pretyping/recordops.cmx engine/proofview.cmx printing/printer.cmx \
    pretyping/pretyping.cmx pretyping/pretype_errors.cmx \
    plugins/ltac/pptactic.cmx printing/ppconstr.cmx lib/pp.cmx \
    proofs/pfedit.cmx clib/option.cmx kernel/names.cmx engine/namegen.cmx \
    vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx lib/loc.cmx \
    library/libnames.cmx library/goptions.cmx proofs/goal.cmx \
    library/globnames.cmx library/global.cmx pretyping/glob_term.cmx \
    pretyping/glob_ops.cmx pretyping/geninterp.cmx interp/genintern.cmx \
    lib/genarg.cmx engine/ftactic.cmx lib/feedback.cmx engine/evd.cmx \
    engine/evarutil.cmx pretyping/evarconv.cmx engine/evar_kinds.cmx \
    kernel/evar.cmx kernel/environ.cmx engine/eConstr.cmx \
    library/decl_kinds.cmx lib/dAst.cmx kernel/conv_oracle.cmx \
    kernel/context.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx kernel/constr.cmx lib/cErrors.cmx lib/cAst.cmx \
    clib/cArray.cmx plugins/ssrmatching/ssrmatching.cmi
plugins/ssrmatching/ssrmatching.cmi : engine/uState.cmi proofs/tacmach.cmi \
    plugins/ltac/tacexpr.cmi proofs/proof_type.cmo lib/pp.cmi \
    kernel/names.cmi kernel/mod_subst.cmi plugins/ltac/ltac_plugin.cmo \
    lib/loc.cmi proofs/goal.cmi pretyping/geninterp.cmi interp/genintern.cmi \
    lib/genarg.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    interp/constrexpr.cmo kernel/constr.cmi
plugins/syntax/ascii_syntax.cmo : lib/util.cmi lib/pp.cmi clib/option.cmi \
    interp/notation.cmi kernel/names.cmi vernac/mltop.cmi \
    library/libnames.cmi clib/int.cmi library/globnames.cmi \
    pretyping/glob_term.cmo lib/dAst.cmi library/coqlib.cmi lib/cErrors.cmi
plugins/syntax/ascii_syntax.cmx : lib/util.cmx lib/pp.cmx clib/option.cmx \
    interp/notation.cmx kernel/names.cmx vernac/mltop.cmx \
    library/libnames.cmx clib/int.cmx library/globnames.cmx \
    pretyping/glob_term.cmx lib/dAst.cmx library/coqlib.cmx lib/cErrors.cmx
plugins/syntax/g_numeral.cmo : vernac/vernacinterp.cmi \
    vernac/vernacentries.cmi stm/vernac_classifier.cmi \
    plugins/ltac/tacexpr.cmi plugins/ltac/tacentries.cmi interp/stdarg.cmi \
    plugins/ltac/pptactic.cmi lib/pp.cmi parsing/pcoq.cmi \
    plugins/syntax/numeral.cmi interp/notation.cmi kernel/names.cmi \
    vernac/mltop.cmi plugins/ltac/ltac_plugin.cmo vernac/locality.cmi \
    pretyping/geninterp.cmi interp/genintern.cmi lib/genarg.cmi \
    engine/ftactic.cmi parsing/extend.cmo parsing/cLexer.cmi
plugins/syntax/g_numeral.cmx : vernac/vernacinterp.cmx \
    vernac/vernacentries.cmx stm/vernac_classifier.cmx \
    plugins/ltac/tacexpr.cmx plugins/ltac/tacentries.cmx interp/stdarg.cmx \
    plugins/ltac/pptactic.cmx lib/pp.cmx parsing/pcoq.cmx \
    plugins/syntax/numeral.cmx interp/notation.cmx kernel/names.cmx \
    vernac/mltop.cmx plugins/ltac/ltac_plugin.cmx vernac/locality.cmx \
    pretyping/geninterp.cmx interp/genintern.cmx lib/genarg.cmx \
    engine/ftactic.cmx parsing/extend.cmx parsing/cLexer.cmx
plugins/syntax/int31_syntax.cmo : lib/pp.cmi interp/notation.cmi \
    kernel/names.cmi vernac/mltop.cmi library/libnames.cmi \
    library/globnames.cmi pretyping/glob_term.cmo lib/dAst.cmi \
    lib/cErrors.cmi clib/bigint.cmi
plugins/syntax/int31_syntax.cmx : lib/pp.cmx interp/notation.cmx \
    kernel/names.cmx vernac/mltop.cmx library/libnames.cmx \
    library/globnames.cmx pretyping/glob_term.cmx lib/dAst.cmx \
    lib/cErrors.cmx clib/bigint.cmx
plugins/syntax/numeral.cmo : lib/util.cmi engine/termops.cmi \
    interp/smartlocate.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    proofs/pfedit.cmi interp/notation.cmi library/nametab.cmi \
    kernel/names.cmi library/libnames.cmi library/globnames.cmi \
    library/global.cmi pretyping/glob_term.cmo kernel/declarations.cmo \
    library/decl_kinds.cmo interp/constrintern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    plugins/syntax/numeral.cmi
plugins/syntax/numeral.cmx : lib/util.cmx engine/termops.cmx \
    interp/smartlocate.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    proofs/pfedit.cmx interp/notation.cmx library/nametab.cmx \
    kernel/names.cmx library/libnames.cmx library/globnames.cmx \
    library/global.cmx pretyping/glob_term.cmx kernel/declarations.cmx \
    library/decl_kinds.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    plugins/syntax/numeral.cmi
plugins/syntax/numeral.cmi : vernac/vernacexpr.cmo interp/notation_term.cmo \
    interp/notation.cmi library/libnames.cmi
plugins/syntax/r_syntax.cmo : lib/util.cmi interp/notation.cmi \
    kernel/names.cmi vernac/mltop.cmi library/libnames.cmi \
    library/globnames.cmi pretyping/glob_term.cmo lib/dAst.cmi \
    clib/bigint.cmi
plugins/syntax/r_syntax.cmx : lib/util.cmx interp/notation.cmx \
    kernel/names.cmx vernac/mltop.cmx library/libnames.cmx \
    library/globnames.cmx pretyping/glob_term.cmx lib/dAst.cmx \
    clib/bigint.cmx
plugins/syntax/string_syntax.cmo : interp/notation.cmi kernel/names.cmi \
    vernac/mltop.cmi library/globnames.cmi pretyping/glob_term.cmo \
    lib/dAst.cmi library/coqlib.cmi plugins/syntax/ascii_syntax_plugin.cmo
plugins/syntax/string_syntax.cmx : interp/notation.cmx kernel/names.cmx \
    vernac/mltop.cmx library/globnames.cmx pretyping/glob_term.cmx \
    lib/dAst.cmx library/coqlib.cmx plugins/syntax/ascii_syntax_plugin.cmx

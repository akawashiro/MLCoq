clib/backtrace.cmo : clib/exninfo.cmi clib/backtrace.cmi
clib/backtrace.cmx : clib/exninfo.cmx clib/backtrace.cmi
clib/backtrace.cmi : clib/exninfo.cmi
clib/bigint.cmo : clib/int.cmi clib/bigint.cmi
clib/bigint.cmx : clib/int.cmx clib/bigint.cmi
clib/bigint.cmi :
clib/cArray.cmo : clib/int.cmi clib/cList.cmi clib/cArray.cmi
clib/cArray.cmx : clib/int.cmx clib/cList.cmx clib/cArray.cmi
clib/cArray.cmi :
clib/cEphemeron.cmo : clib/cEphemeron.cmi
clib/cEphemeron.cmx : clib/cEphemeron.cmi
clib/cEphemeron.cmi :
clib/cList.cmo : clib/int.cmi clib/cSig.cmi clib/cList.cmi
clib/cList.cmx : clib/int.cmx clib/cSig.cmi clib/cList.cmi
clib/cList.cmi : clib/cSig.cmi
clib/cMap.cmo : clib/cSig.cmi clib/cMap.cmi
clib/cMap.cmx : clib/cSig.cmi clib/cMap.cmi
clib/cMap.cmi : clib/cSig.cmi
clib/cObj.cmo : clib/cObj.cmi
clib/cObj.cmx : clib/cObj.cmi
clib/cObj.cmi :
clib/cSet.cmo : clib/hashset.cmi clib/hashcons.cmi clib/cSet.cmi
clib/cSet.cmx : clib/hashset.cmx clib/hashcons.cmx clib/cSet.cmi
clib/cSet.cmi : clib/hashcons.cmi
clib/cSig.cmi :
clib/cStack.cmo : clib/cList.cmi clib/cStack.cmi
clib/cStack.cmx : clib/cList.cmx clib/cStack.cmi
clib/cStack.cmi : clib/cSig.cmi
clib/cString.cmo : clib/int.cmi clib/hashcons.cmi clib/cMap.cmi \
    clib/cList.cmi clib/cString.cmi
clib/cString.cmx : clib/int.cmx clib/hashcons.cmx clib/cMap.cmx \
    clib/cList.cmx clib/cString.cmi
clib/cString.cmi : clib/cMap.cmi clib/cList.cmi
clib/cThread.cmo : clib/cThread.cmi
clib/cThread.cmx : clib/cThread.cmi
clib/cThread.cmi :
clib/cUnix.cmo : clib/cString.cmi clib/cUnix.cmi
clib/cUnix.cmx : clib/cString.cmx clib/cUnix.cmi
clib/cUnix.cmi :
clib/diff2.cmo : clib/diff2.cmi
clib/diff2.cmx : clib/diff2.cmi
clib/diff2.cmi :
clib/dyn.cmo : clib/int.cmi clib/cSig.cmi clib/dyn.cmi
clib/dyn.cmx : clib/int.cmx clib/cSig.cmi clib/dyn.cmi
clib/dyn.cmi : clib/cSig.cmi
clib/exninfo.cmo : clib/store.cmi clib/exninfo.cmi
clib/exninfo.cmx : clib/store.cmx clib/exninfo.cmi
clib/exninfo.cmi :
clib/hMap.cmo : clib/int.cmi clib/cMap.cmi clib/hMap.cmi
clib/hMap.cmx : clib/int.cmx clib/cMap.cmx clib/hMap.cmi
clib/hMap.cmi : clib/cMap.cmi
clib/hashcons.cmo : clib/hashset.cmi clib/hashcons.cmi
clib/hashcons.cmx : clib/hashset.cmx clib/hashcons.cmi
clib/hashcons.cmi : clib/hashset.cmi
clib/hashset.cmo : clib/int.cmi clib/hashset.cmi
clib/hashset.cmx : clib/int.cmx clib/hashset.cmi
clib/hashset.cmi :
clib/heap.cmo : clib/heap.cmi
clib/heap.cmx : clib/heap.cmi
clib/heap.cmi :
clib/iStream.cmo : clib/iStream.cmi
clib/iStream.cmx : clib/iStream.cmi
clib/iStream.cmi :
clib/int.cmo : clib/cMap.cmi clib/int.cmi
clib/int.cmx : clib/cMap.cmx clib/int.cmi
clib/int.cmi : clib/cMap.cmi
clib/minisys.cmo : clib/unicode.cmi
clib/minisys.cmx : clib/unicode.cmx
clib/monad.cmo : clib/monad.cmi
clib/monad.cmx : clib/monad.cmi
clib/monad.cmi :
clib/option.cmo : clib/option.cmi
clib/option.cmx : clib/option.cmi
clib/option.cmi :
clib/orderedType.cmo : clib/int.cmi clib/orderedType.cmi
clib/orderedType.cmx : clib/int.cmx clib/orderedType.cmi
clib/orderedType.cmi :
clib/predicate.cmo : clib/predicate.cmi
clib/predicate.cmx : clib/predicate.cmi
clib/predicate.cmi :
clib/range.cmo : clib/int.cmi clib/range.cmi
clib/range.cmx : clib/int.cmx clib/range.cmi
clib/range.cmi :
clib/segmenttree.cmo : clib/segmenttree.cmi
clib/segmenttree.cmx : clib/segmenttree.cmi
clib/segmenttree.cmi :
clib/store.cmo : clib/store.cmi
clib/store.cmx : clib/store.cmi
clib/store.cmi :
clib/terminal.cmo : clib/terminal.cmi
clib/terminal.cmx : clib/terminal.cmi
clib/terminal.cmi :
clib/trie.cmo : clib/trie.cmi
clib/trie.cmx : clib/trie.cmi
clib/trie.cmi :
clib/unicode.cmo : clib/unicodetable.cmo clib/segmenttree.cmi \
    clib/unicode.cmi
clib/unicode.cmx : clib/unicodetable.cmx clib/segmenttree.cmx \
    clib/unicode.cmi
clib/unicode.cmi :
clib/unicodetable.cmo :
clib/unicodetable.cmx :
clib/unionfind.cmo : clib/unionfind.cmi
clib/unionfind.cmx : clib/unionfind.cmi
clib/unionfind.cmi :
config/coq_config.cmo : config/coq_config.cmi
config/coq_config.cmx : config/coq_config.cmi
config/coq_config.cmi :
configure.cmo :
configure.cmx :
coqpp/coqpp_ast.cmi :
coqpp/coqpp_lex.cmo : coqpp/coqpp_parse.cmi coqpp/coqpp_ast.cmi
coqpp/coqpp_lex.cmx : coqpp/coqpp_parse.cmx coqpp/coqpp_ast.cmi
coqpp/coqpp_main.cmo : coqpp/coqpp_parse.cmi coqpp/coqpp_lex.cmo \
    coqpp/coqpp_ast.cmi
coqpp/coqpp_main.cmx : coqpp/coqpp_parse.cmx coqpp/coqpp_lex.cmx \
    coqpp/coqpp_ast.cmi
coqpp/coqpp_parse.cmo : coqpp/coqpp_ast.cmi coqpp/coqpp_parse.cmi
coqpp/coqpp_parse.cmx : coqpp/coqpp_ast.cmi coqpp/coqpp_parse.cmi
coqpp/coqpp_parse.cmi : coqpp/coqpp_ast.cmi
dev/checker_printers.cmo : kernel/univ.cmi lib/pp.cmi kernel/names.cmi \
    lib/loc.cmi clib/int.cmi lib/future.cmi clib/bigint.cmi \
    dev/checker_printers.cmi
dev/checker_printers.cmx : kernel/univ.cmx lib/pp.cmx kernel/names.cmx \
    lib/loc.cmx clib/int.cmx lib/future.cmx clib/bigint.cmx \
    dev/checker_printers.cmi
dev/checker_printers.cmi : kernel/univ.cmi lib/pp.cmi kernel/names.cmi \
    lib/loc.cmi clib/int.cmi lib/future.cmi clib/bigint.cmi
dev/dynlink.cmo :
dev/dynlink.cmx :
dev/header.cmo :
dev/header.cmx :
dev/top_printers.cmo : vernac/vernacinterp.cmi lib/util.cmi \
    engine/univSubst.cmi engine/univProblem.cmi engine/univNames.cmi \
    kernel/univ.cmi kernel/uGraph.cmi vernac/topfmt.cmi engine/termops.cmi \
    interp/stdarg.cmi kernel/sorts.cmi lib/rtree.cmi proofs/refiner.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi proofs/proof.cmi \
    printing/printer.cmi printing/ppconstr.cmi lib/pp.cmi proofs/pfedit.cmi \
    parsing/pcoq.cmi kernel/names.cmi kernel/mod_subst.cmi \
    pretyping/ltac_pretype.cmo plugins/ltac/ltac_plugin.cmo lib/loc.cmi \
    library/libobject.cmi library/libnames.cmi clib/int.cmi \
    tactics/ind_tables.cmi tactics/hints.cmi library/goptions.cmi \
    proofs/goal.cmi library/globnames.cmi library/global.cmi \
    pretyping/geninterp.cmi lib/genarg.cmi lib/future.cmi lib/flags.cmi \
    parsing/extend.cmo engine/evd.cmi kernel/evar.cmi kernel/environ.cmi \
    vernac/egramml.cmi engine/eConstr.cmi pretyping/detyping.cmi \
    kernel/declarations.cmo interp/constrintern.cmi interp/constrextern.cmi \
    kernel/constr.cmi proofs/clenv.cmi pretyping/classops.cmi lib/cErrors.cmi \
    kernel/cClosure.cmi clib/bigint.cmi dev/top_printers.cmi
dev/top_printers.cmx : vernac/vernacinterp.cmx lib/util.cmx \
    engine/univSubst.cmx engine/univProblem.cmx engine/univNames.cmx \
    kernel/univ.cmx kernel/uGraph.cmx vernac/topfmt.cmx engine/termops.cmx \
    interp/stdarg.cmx kernel/sorts.cmx lib/rtree.cmx proofs/refiner.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx proofs/proof.cmx \
    printing/printer.cmx printing/ppconstr.cmx lib/pp.cmx proofs/pfedit.cmx \
    parsing/pcoq.cmx kernel/names.cmx kernel/mod_subst.cmx \
    pretyping/ltac_pretype.cmx plugins/ltac/ltac_plugin.cmx lib/loc.cmx \
    library/libobject.cmx library/libnames.cmx clib/int.cmx \
    tactics/ind_tables.cmx tactics/hints.cmx library/goptions.cmx \
    proofs/goal.cmx library/globnames.cmx library/global.cmx \
    pretyping/geninterp.cmx lib/genarg.cmx lib/future.cmx lib/flags.cmx \
    parsing/extend.cmx engine/evd.cmx kernel/evar.cmx kernel/environ.cmx \
    vernac/egramml.cmx engine/eConstr.cmx pretyping/detyping.cmx \
    kernel/declarations.cmx interp/constrintern.cmx interp/constrextern.cmx \
    kernel/constr.cmx proofs/clenv.cmx pretyping/classops.cmx lib/cErrors.cmx \
    kernel/cClosure.cmx clib/bigint.cmx dev/top_printers.cmi
dev/top_printers.cmi : engine/univSubst.cmi engine/univProblem.cmi \
    kernel/univ.cmi engine/uState.cmi kernel/uGraph.cmi lib/rtree.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi proofs/proof_type.cmo \
    proofs/proof.cmi lib/pp.cmi pretyping/pattern.cmo kernel/names.cmi \
    kernel/mod_subst.cmi pretyping/ltac_pretype.cmo \
    plugins/ltac/ltac_plugin.cmo lib/loc.cmi library/libobject.cmi \
    library/libnames.cmi clib/int.cmi tactics/ind_tables.cmi \
    tactics/hints.cmi proofs/goal.cmi pretyping/glob_term.cmo \
    pretyping/geninterp.cmi lib/genarg.cmi lib/future.cmi engine/evd.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declarations.cmo interp/constrexpr.cmo kernel/constr.cmi \
    proofs/clenv.cmi pretyping/classops.cmi kernel/cClosure.cmi \
    clib/bigint.cmi
dev/vm_printers.cmo : kernel/vmvalues.cmi kernel/univ.cmi kernel/term.cmi \
    kernel/names.cmi lib/feedback.cmi kernel/evar.cmi kernel/constr.cmi \
    kernel/cemitcodes.cmi
dev/vm_printers.cmx : kernel/vmvalues.cmx kernel/univ.cmx kernel/term.cmx \
    kernel/names.cmx lib/feedback.cmx kernel/evar.cmx kernel/constr.cmx \
    kernel/cemitcodes.cmx
engine/eConstr.cmo : kernel/vars.cmi lib/util.cmi engine/univProblem.cmi \
    kernel/univ.cmi kernel/sorts.cmi kernel/reduction.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi library/globnames.cmi engine/evd.cmi \
    kernel/environ.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi clib/cArray.cmi engine/eConstr.cmi
engine/eConstr.cmx : kernel/vars.cmx lib/util.cmx engine/univProblem.cmx \
    kernel/univ.cmx kernel/sorts.cmx kernel/reduction.cmx lib/pp.cmx \
    kernel/names.cmx clib/int.cmx library/globnames.cmx engine/evd.cmx \
    kernel/environ.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx clib/cArray.cmx engine/eConstr.cmi
engine/eConstr.cmi : engine/univProblem.cmi kernel/univ.cmi kernel/term.cmi \
    kernel/sorts.cmi kernel/names.cmi lib/loc.cmi engine/evd.cmi \
    kernel/environ.cmi kernel/context.cmi kernel/constr.cmi clib/cSig.cmi
engine/evar_kinds.cmo : kernel/names.cmi kernel/evar.cmi \
    engine/evar_kinds.cmi
engine/evar_kinds.cmx : kernel/names.cmx kernel/evar.cmx \
    engine/evar_kinds.cmi
engine/evar_kinds.cmi : kernel/names.cmi kernel/evar.cmi
engine/evarutil.cmo : kernel/vars.cmi lib/util.cmi engine/univSubst.cmi \
    engine/univProblem.cmi kernel/univ.cmi engine/termops.cmi kernel/term.cmi \
    library/summary.cmi clib/store.cmi kernel/reduction.cmi lib/pp.cmi \
    clib/option.cmi kernel/names.cmi engine/namegen.cmi lib/loc.cmi \
    clib/int.cmi library/globnames.cmi library/global.cmi lib/flags.cmi \
    engine/evd.cmi engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    engine/evarutil.cmi
engine/evarutil.cmx : kernel/vars.cmx lib/util.cmx engine/univSubst.cmx \
    engine/univProblem.cmx kernel/univ.cmx engine/termops.cmx kernel/term.cmx \
    library/summary.cmx clib/store.cmx kernel/reduction.cmx lib/pp.cmx \
    clib/option.cmx kernel/names.cmx engine/namegen.cmx lib/loc.cmx \
    clib/int.cmx library/globnames.cmx library/global.cmx lib/flags.cmx \
    engine/evd.cmx engine/evar_kinds.cmx kernel/evar.cmx kernel/environ.cmx \
    engine/eConstr.cmx kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    engine/evarutil.cmi
engine/evarutil.cmi : lib/util.cmi engine/univSubst.cmi kernel/univ.cmi \
    library/summary.cmi clib/store.cmi kernel/sorts.cmi kernel/reduction.cmi \
    kernel/names.cmi engine/namegen.cmi lib/loc.cmi engine/evd.cmi \
    engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi
engine/evd.cmo : kernel/vars.cmi lib/util.cmi engine/univSubst.cmi \
    engine/univProblem.cmi engine/univGen.cmi kernel/univ.cmi \
    engine/uState.cmi kernel/uGraph.cmi kernel/term.cmi library/summary.cmi \
    clib/store.cmi kernel/sorts.cmi kernel/safe_typing.cmi \
    kernel/reduction.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/nameops.cmi clib/monad.cmi lib/loc.cmi clib/int.cmi \
    library/global.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi kernel/context.cmi kernel/constr.cmi clib/cList.cmi \
    lib/cErrors.cmi clib/cArray.cmi engine/evd.cmi
engine/evd.cmx : kernel/vars.cmx lib/util.cmx engine/univSubst.cmx \
    engine/univProblem.cmx engine/univGen.cmx kernel/univ.cmx \
    engine/uState.cmx kernel/uGraph.cmx kernel/term.cmx library/summary.cmx \
    clib/store.cmx kernel/sorts.cmx kernel/safe_typing.cmx \
    kernel/reduction.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/nameops.cmx clib/monad.cmx lib/loc.cmx clib/int.cmx \
    library/global.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    kernel/environ.cmx kernel/context.cmx kernel/constr.cmx clib/cList.cmx \
    lib/cErrors.cmx clib/cArray.cmx engine/evd.cmi
engine/evd.cmi : lib/util.cmi engine/univSubst.cmi engine/univProblem.cmi \
    engine/univNames.cmi kernel/univ.cmi engine/uState.cmi kernel/uGraph.cmi \
    kernel/term.cmi library/summary.cmi clib/store.cmi kernel/sorts.cmi \
    kernel/safe_typing.cmi kernel/reduction.cmi kernel/names.cmi \
    clib/monad.cmi lib/loc.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi kernel/entries.cmo kernel/context.cmi \
    kernel/constr.cmi
engine/ftactic.cmo : engine/proofview.cmi clib/monad.cmi engine/ftactic.cmi
engine/ftactic.cmx : engine/proofview.cmx clib/monad.cmx engine/ftactic.cmi
engine/ftactic.cmi : engine/proofview.cmi clib/monad.cmi kernel/environ.cmi
engine/logic_monad.cmo : lib/util.cmi lib/pp.cmi clib/monad.cmi \
    lib/feedback.cmi clib/exninfo.cmi lib/control.cmi lib/cErrors.cmi \
    engine/logic_monad.cmi
engine/logic_monad.cmx : lib/util.cmx lib/pp.cmx clib/monad.cmx \
    lib/feedback.cmx clib/exninfo.cmx lib/control.cmx lib/cErrors.cmx \
    engine/logic_monad.cmi
engine/logic_monad.cmi : lib/pp.cmi clib/monad.cmi clib/exninfo.cmi
engine/namegen.cmo : kernel/vars.cmi lib/util.cmi clib/unicode.cmi \
    kernel/term.cmi lib/pp.cmi library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi library/libnames.cmi library/lib.cmi clib/int.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    lib/flags.cmi kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi engine/namegen.cmi
engine/namegen.cmx : kernel/vars.cmx lib/util.cmx clib/unicode.cmx \
    kernel/term.cmx lib/pp.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx library/libnames.cmx library/lib.cmx clib/int.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    lib/flags.cmx kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx engine/namegen.cmi
engine/namegen.cmi : kernel/sorts.cmi kernel/names.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi
engine/nameops.cmo : lib/util.cmi lib/pp.cmi kernel/names.cmi clib/int.cmi \
    engine/nameops.cmi
engine/nameops.cmx : lib/util.cmx lib/pp.cmx kernel/names.cmx clib/int.cmx \
    engine/nameops.cmi
engine/nameops.cmi : lib/pp.cmi kernel/names.cmi kernel/constr.cmi
engine/proofview.cmo : lib/util.cmi lib/system.cmi \
    engine/proofview_monad.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/logic_monad.cmi lib/loc.cmi clib/int.cmi library/global.cmi \
    lib/feedback.cmi clib/exninfo.cmi engine/evd.cmi engine/evarutil.cmi \
    engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi lib/control.cmi kernel/context.cmi kernel/constr.cmi \
    clib/cList.cmi lib/cErrors.cmi engine/proofview.cmi
engine/proofview.cmx : lib/util.cmx lib/system.cmx \
    engine/proofview_monad.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/logic_monad.cmx lib/loc.cmx clib/int.cmx library/global.cmx \
    lib/feedback.cmx clib/exninfo.cmx engine/evd.cmx engine/evarutil.cmx \
    engine/evar_kinds.cmx kernel/evar.cmx kernel/environ.cmx \
    engine/eConstr.cmx lib/control.cmx kernel/context.cmx kernel/constr.cmx \
    clib/cList.cmx lib/cErrors.cmx engine/proofview.cmi
engine/proofview.cmi : lib/util.cmi engine/uState.cmi kernel/safe_typing.cmi \
    engine/proofview_monad.cmi lib/pp.cmi kernel/names.cmi clib/monad.cmi \
    engine/logic_monad.cmi proofs/goal.cmi clib/exninfo.cmi engine/evd.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi
engine/proofview_monad.cmo : clib/store.cmi lib/pp.cmi \
    engine/logic_monad.cmi engine/evd.cmi kernel/evar.cmi kernel/environ.cmi \
    clib/cList.cmi engine/proofview_monad.cmi
engine/proofview_monad.cmx : clib/store.cmx lib/pp.cmx \
    engine/logic_monad.cmx engine/evd.cmx kernel/evar.cmx kernel/environ.cmx \
    clib/cList.cmx engine/proofview_monad.cmi
engine/proofview_monad.cmi : clib/store.cmi lib/pp.cmi \
    engine/logic_monad.cmi engine/evd.cmi kernel/evar.cmi kernel/environ.cmi
engine/termops.cmo : kernel/vars.cmi lib/util.cmi engine/univSubst.cmi \
    engine/univNames.cmi kernel/univ.cmi engine/uState.cmi kernel/term.cmi \
    kernel/reduction.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi clib/int.cmi library/globnames.cmi \
    library/global.cmi engine/evd.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi clib/cArray.cmi engine/termops.cmi
engine/termops.cmx : kernel/vars.cmx lib/util.cmx engine/univSubst.cmx \
    engine/univNames.cmx kernel/univ.cmx engine/uState.cmx kernel/term.cmx \
    kernel/reduction.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx clib/int.cmx library/globnames.cmx \
    library/global.cmx engine/evd.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx clib/cArray.cmx engine/termops.cmi
engine/termops.cmi : kernel/univ.cmi engine/uState.cmi kernel/sorts.cmi \
    kernel/reduction.cmi lib/pp.cmi kernel/names.cmi library/libnames.cmi \
    clib/int.cmi engine/evd.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/context.cmi kernel/constr.cmi
engine/uState.cmo : lib/util.cmi engine/univops.cmi engine/univSubst.cmi \
    engine/univProblem.cmi engine/univNames.cmi engine/univMinim.cmi \
    engine/univGen.cmi kernel/univ.cmi kernel/uGraph.cmi kernel/sorts.cmi \
    kernel/safe_typing.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    lib/loc.cmi library/libnames.cmi kernel/environ.cmi kernel/entries.cmo \
    clib/cString.cmi lib/cErrors.cmi lib/cAst.cmi engine/uState.cmi
engine/uState.cmx : lib/util.cmx engine/univops.cmx engine/univSubst.cmx \
    engine/univProblem.cmx engine/univNames.cmx engine/univMinim.cmx \
    engine/univGen.cmx kernel/univ.cmx kernel/uGraph.cmx kernel/sorts.cmx \
    kernel/safe_typing.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    lib/loc.cmx library/libnames.cmx kernel/environ.cmx kernel/entries.cmx \
    clib/cString.cmx lib/cErrors.cmx lib/cAst.cmx engine/uState.cmi
engine/uState.cmi : engine/univSubst.cmi engine/univProblem.cmi \
    engine/univNames.cmi kernel/univ.cmi kernel/uGraph.cmi kernel/sorts.cmi \
    kernel/safe_typing.cmi lib/pp.cmi kernel/names.cmi lib/loc.cmi \
    library/libnames.cmi kernel/environ.cmi kernel/entries.cmo
engine/univGen.cmo : kernel/vars.cmi kernel/univ.cmi kernel/sorts.cmi \
    lib/remoteCounter.cmi lib/pp.cmi library/nametab.cmi kernel/names.cmi \
    kernel/inductive.cmi library/globnames.cmi library/global.cmi \
    kernel/environ.cmi kernel/declarations.cmo kernel/constr.cmi \
    lib/cErrors.cmi engine/univGen.cmi
engine/univGen.cmx : kernel/vars.cmx kernel/univ.cmx kernel/sorts.cmx \
    lib/remoteCounter.cmx lib/pp.cmx library/nametab.cmx kernel/names.cmx \
    kernel/inductive.cmx library/globnames.cmx library/global.cmx \
    kernel/environ.cmx kernel/declarations.cmx kernel/constr.cmx \
    lib/cErrors.cmx engine/univGen.cmi
engine/univGen.cmi : kernel/univ.cmi kernel/sorts.cmi lib/remoteCounter.cmi \
    kernel/names.cmi library/globnames.cmi kernel/environ.cmi \
    kernel/constr.cmi
engine/univMinim.cmo : engine/univSubst.cmi kernel/univ.cmi \
    kernel/uGraph.cmi lib/pp.cmi clib/orderedType.cmi library/goptions.cmi \
    clib/cList.cmi engine/univMinim.cmi
engine/univMinim.cmx : engine/univSubst.cmx kernel/univ.cmx \
    kernel/uGraph.cmx lib/pp.cmx clib/orderedType.cmx library/goptions.cmx \
    clib/cList.cmx engine/univMinim.cmi
engine/univMinim.cmi : engine/univSubst.cmi kernel/univ.cmi \
    kernel/uGraph.cmi clib/cSet.cmi
engine/univNames.cmo : kernel/univ.cmi library/summary.cmi lib/pp.cmi \
    library/nametab.cmi kernel/names.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi clib/int.cmi library/globnames.cmi \
    lib/cErrors.cmi lib/cAst.cmi engine/univNames.cmi
engine/univNames.cmx : kernel/univ.cmx library/summary.cmx lib/pp.cmx \
    library/nametab.cmx kernel/names.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx library/globnames.cmx \
    lib/cErrors.cmx lib/cAst.cmx engine/univNames.cmi
engine/univNames.cmi : kernel/univ.cmi lib/pp.cmi kernel/names.cmi \
    library/libnames.cmi library/decl_kinds.cmo
engine/univProblem.cmo : engine/univSubst.cmi kernel/univ.cmi \
    kernel/uGraph.cmi kernel/sorts.cmi lib/pp.cmi clib/option.cmi \
    clib/int.cmi kernel/constr.cmi lib/cErrors.cmi clib/cArray.cmi \
    engine/univProblem.cmi
engine/univProblem.cmx : engine/univSubst.cmx kernel/univ.cmx \
    kernel/uGraph.cmx kernel/sorts.cmx lib/pp.cmx clib/option.cmx \
    clib/int.cmx kernel/constr.cmx lib/cErrors.cmx clib/cArray.cmx \
    engine/univProblem.cmi
engine/univProblem.cmi : kernel/univ.cmi kernel/uGraph.cmi kernel/sorts.cmi \
    lib/pp.cmi kernel/constr.cmi
engine/univSubst.cmo : lib/util.cmi kernel/univ.cmi kernel/sorts.cmi \
    lib/pp.cmi lib/flags.cmi kernel/constr.cmi lib/cProfile.cmi \
    engine/univSubst.cmi
engine/univSubst.cmx : lib/util.cmx kernel/univ.cmx kernel/sorts.cmx \
    lib/pp.cmx lib/flags.cmx kernel/constr.cmx lib/cProfile.cmx \
    engine/univSubst.cmi
engine/univSubst.cmi : kernel/univ.cmi lib/pp.cmi kernel/constr.cmi
engine/universes.cmo : engine/univSubst.cmi engine/univProblem.cmi \
    engine/univNames.cmi engine/univMinim.cmi engine/univGen.cmi \
    kernel/univ.cmi engine/universes.cmi
engine/universes.cmx : engine/univSubst.cmx engine/univProblem.cmx \
    engine/univNames.cmx engine/univMinim.cmx engine/univGen.cmx \
    kernel/univ.cmx engine/universes.cmi
engine/universes.cmi : engine/univSubst.cmi engine/univProblem.cmi \
    engine/univNames.cmi engine/univMinim.cmi engine/univGen.cmi \
    kernel/univ.cmi kernel/uGraph.cmi kernel/sorts.cmi lib/remoteCounter.cmi \
    lib/pp.cmi kernel/names.cmi library/libnames.cmi library/globnames.cmi \
    kernel/environ.cmi library/decl_kinds.cmo kernel/constr.cmi
engine/univops.cmo : kernel/univ.cmi kernel/uGraph.cmi kernel/sorts.cmi \
    kernel/constr.cmi engine/univops.cmi
engine/univops.cmx : kernel/univ.cmx kernel/uGraph.cmx kernel/sorts.cmx \
    kernel/constr.cmx engine/univops.cmi
engine/univops.cmi : kernel/univ.cmi kernel/constr.cmi
grammar/q_util.cmi :
ide/config_lexer.cmo : lib/util.cmi ide/config_lexer.cmi
ide/config_lexer.cmx : lib/util.cmx ide/config_lexer.cmi
ide/config_lexer.cmi : lib/util.cmi
ide/configwin.cmo : ide/configwin_types.cmo ide/configwin_ihm.cmi \
    ide/configwin.cmi
ide/configwin.cmx : ide/configwin_types.cmx ide/configwin_ihm.cmx \
    ide/configwin.cmi
ide/configwin.cmi :
ide/configwin_ihm.cmo : ide/minilib.cmi ide/configwin_types.cmo \
    ide/configwin_messages.cmo ide/configwin_ihm.cmi
ide/configwin_ihm.cmx : ide/minilib.cmx ide/configwin_types.cmx \
    ide/configwin_messages.cmx ide/configwin_ihm.cmi
ide/configwin_ihm.cmi : ide/configwin_types.cmo
ide/configwin_messages.cmo : clib/option.cmi
ide/configwin_messages.cmx : clib/option.cmx
ide/configwin_types.cmo :
ide/configwin_types.cmx :
ide/coq.cmo : ide/protocol/xmlprotocol.cmi ide/protocol/xml_printer.cmi \
    ide/protocol/xml_parser.cmi lib/spawn.cmi ide/protocol/serialize.cmi \
    ide/preferences.cmi clib/option.cmi ide/minilib.cmi \
    ide/protocol/interface.cmo ide/ideutils.cmi lib/feedback.cmi \
    config/coq_config.cmi ide/coq.cmi
ide/coq.cmx : ide/protocol/xmlprotocol.cmx ide/protocol/xml_printer.cmx \
    ide/protocol/xml_parser.cmx lib/spawn.cmx ide/protocol/serialize.cmx \
    ide/preferences.cmx clib/option.cmx ide/minilib.cmx \
    ide/protocol/interface.cmx ide/ideutils.cmx lib/feedback.cmx \
    config/coq_config.cmx ide/coq.cmi
ide/coq.cmi : ide/protocol/interface.cmo lib/feedback.cmi
ide/coqOps.cmo : ide/wg_Segment.cmi ide/wg_ScriptView.cmi \
    ide/wg_RoutedMessageViews.cmi ide/wg_ProofView.cmi lib/util.cmi \
    ide/tags.cmi lib/stateid.cmi ide/sentence.cmi ide/preferences.cmi \
    lib/pp.cmi clib/option.cmi ide/minilib.cmi lib/loc.cmi \
    ide/protocol/interface.cmo clib/int.cmi ide/ideutils.cmi lib/feedback.cmi \
    ide/document.cmi ide/coq.cmi clib/cString.cmi clib/cSig.cmi \
    clib/cList.cmi ide/coqOps.cmi
ide/coqOps.cmx : ide/wg_Segment.cmx ide/wg_ScriptView.cmx \
    ide/wg_RoutedMessageViews.cmx ide/wg_ProofView.cmx lib/util.cmx \
    ide/tags.cmx lib/stateid.cmx ide/sentence.cmx ide/preferences.cmx \
    lib/pp.cmx clib/option.cmx ide/minilib.cmx lib/loc.cmx \
    ide/protocol/interface.cmx clib/int.cmx ide/ideutils.cmx lib/feedback.cmx \
    ide/document.cmx ide/coq.cmx clib/cString.cmx clib/cSig.cmi \
    clib/cList.cmx ide/coqOps.cmi
ide/coqOps.cmi : ide/wg_Segment.cmi ide/wg_ScriptView.cmi \
    ide/wg_RoutedMessageViews.cmi ide/wg_ProofView.cmi \
    ide/protocol/interface.cmo ide/coq.cmi clib/cString.cmi
ide/coq_commands.cmo : ide/coq_commands.cmi
ide/coq_commands.cmx : ide/coq_commands.cmi
ide/coq_commands.cmi :
ide/coq_lex.cmo : ide/tags.cmi ide/coq_lex.cmi
ide/coq_lex.cmx : ide/tags.cmx ide/coq_lex.cmi
ide/coq_lex.cmi :
ide/coqide.cmo : ide/wg_Notebook.cmi lib/util.cmi ide/tags.cmi \
    ide/session.cmi ide/sentence.cmi ide/preferences.cmi lib/pp.cmi \
    clib/option.cmi ide/nanoPG.cmi ide/minilib.cmi ide/protocol/interface.cmo \
    ide/ideutils.cmi ide/gtk_parsing.cmi lib/flags.cmi ide/fileOps.cmi \
    lib/feedback.cmi ide/coqide_ui.cmi config/coq_config.cmi \
    ide/coq_commands.cmi lib/coqProject_file.cmi ide/coq.cmi clib/cUnix.cmi \
    clib/cString.cmi clib/backtrace.cmi ide/coqide.cmi
ide/coqide.cmx : ide/wg_Notebook.cmx lib/util.cmx ide/tags.cmx \
    ide/session.cmx ide/sentence.cmx ide/preferences.cmx lib/pp.cmx \
    clib/option.cmx ide/nanoPG.cmx ide/minilib.cmx ide/protocol/interface.cmx \
    ide/ideutils.cmx ide/gtk_parsing.cmx lib/flags.cmx ide/fileOps.cmx \
    lib/feedback.cmx ide/coqide_ui.cmx config/coq_config.cmx \
    ide/coq_commands.cmx lib/coqProject_file.cmx ide/coq.cmx clib/cUnix.cmx \
    clib/cString.cmx clib/backtrace.cmx ide/coqide.cmi
ide/coqide.cmi :
ide/coqide_main.cmo : ide/preferences.cmi ide/minilib.cmi ide/ideutils.cmi \
    lib/flags.cmi ide/coqide.cmi ide/coq.cmi ide/coqide_main.cmi
ide/coqide_main.cmx : ide/preferences.cmx ide/minilib.cmx ide/ideutils.cmx \
    lib/flags.cmx ide/coqide.cmx ide/coq.cmx ide/coqide_main.cmi
ide/coqide_main.cmi :
ide/coqide_ui.cmo : lib/util.cmi ide/preferences.cmi config/coq_config.cmi \
    ide/coq_commands.cmi ide/coqide_ui.cmi
ide/coqide_ui.cmx : lib/util.cmx ide/preferences.cmx config/coq_config.cmx \
    ide/coq_commands.cmx ide/coqide_ui.cmi
ide/coqide_ui.cmi :
ide/document.cmo : lib/stateid.cmi lib/pp.cmi clib/option.cmi clib/cSig.cmi \
    clib/cList.cmi ide/document.cmi
ide/document.cmx : lib/stateid.cmx lib/pp.cmx clib/option.cmx clib/cSig.cmi \
    clib/cList.cmx ide/document.cmi
ide/document.cmi : lib/stateid.cmi lib/pp.cmi
ide/fileOps.cmo : ide/sentence.cmi ide/preferences.cmi ide/minilib.cmi \
    ide/ideutils.cmi ide/fileOps.cmi
ide/fileOps.cmx : ide/sentence.cmx ide/preferences.cmx ide/minilib.cmx \
    ide/ideutils.cmx ide/fileOps.cmi
ide/fileOps.cmi : ide/ideutils.cmi
ide/gtk_parsing.cmo : ide/minilib.cmi ide/gtk_parsing.cmi
ide/gtk_parsing.cmx : ide/minilib.cmx ide/gtk_parsing.cmi
ide/gtk_parsing.cmi :
ide/idetop.cmo : ide/protocol/xmlprotocol.cmi ide/protocol/xml_printer.cmi \
    ide/protocol/xml_parser.cmi lib/xml_datatype.cmi vernac/vernacprop.cmi \
    vernac/vernacexpr.cmo vernac/vernacentries.cmi toplevel/vernac.cmi \
    lib/util.cmi toplevel/usage.cmi vernac/topfmt.cmi engine/termops.cmi \
    stm/stm.cmi lib/stateid.cmi stm/spawned.cmi ide/protocol/serialize.cmi \
    vernac/search.cmi ide/protocol/richpp.cmi proofs/proof_global.cmi \
    printing/proof_diffs.cmi proofs/proof.cmi printing/printer.cmi \
    vernac/ppvernac.cmi lib/pp_diff.cmi lib/pp.cmi parsing/pcoq.cmi \
    clib/option.cmi library/nametab.cmi kernel/names.cmi lib/loc.cmi \
    library/lib.cmi ide/protocol/interface.cmo library/goptions.cmi \
    proofs/goal.cmi library/global.cmi lib/flags.cmi lib/feedback.cmi \
    engine/evd.cmi kernel/evar.cmi kernel/environ.cmi stm/coqworkmgrApi.cmi \
    toplevel/coqtop.cmi config/coq_config.cmi lib/control.cmi \
    kernel/context.cmi interp/constrintern.cmi clib/cThread.cmi clib/cSig.cmi \
    lib/cErrors.cmi lib/cAst.cmi
ide/idetop.cmx : ide/protocol/xmlprotocol.cmx ide/protocol/xml_printer.cmx \
    ide/protocol/xml_parser.cmx lib/xml_datatype.cmi vernac/vernacprop.cmx \
    vernac/vernacexpr.cmx vernac/vernacentries.cmx toplevel/vernac.cmx \
    lib/util.cmx toplevel/usage.cmx vernac/topfmt.cmx engine/termops.cmx \
    stm/stm.cmx lib/stateid.cmx stm/spawned.cmx ide/protocol/serialize.cmx \
    vernac/search.cmx ide/protocol/richpp.cmx proofs/proof_global.cmx \
    printing/proof_diffs.cmx proofs/proof.cmx printing/printer.cmx \
    vernac/ppvernac.cmx lib/pp_diff.cmx lib/pp.cmx parsing/pcoq.cmx \
    clib/option.cmx library/nametab.cmx kernel/names.cmx lib/loc.cmx \
    library/lib.cmx ide/protocol/interface.cmx library/goptions.cmx \
    proofs/goal.cmx library/global.cmx lib/flags.cmx lib/feedback.cmx \
    engine/evd.cmx kernel/evar.cmx kernel/environ.cmx stm/coqworkmgrApi.cmx \
    toplevel/coqtop.cmx config/coq_config.cmx lib/control.cmx \
    kernel/context.cmx interp/constrintern.cmx clib/cThread.cmx clib/cSig.cmi \
    lib/cErrors.cmx lib/cAst.cmx
ide/ideutils.cmo : lib/xml_datatype.cmi lib/util.cmi ide/utf8_convert.cmi \
    lib/system.cmi ide/preferences.cmi lib/pp.cmi ide/minilib.cmi \
    lib/feedback.cmi lib/envars.cmi config/coq_config.cmi clib/cList.cmi \
    ide/ideutils.cmi
ide/ideutils.cmx : lib/xml_datatype.cmi lib/util.cmx ide/utf8_convert.cmx \
    lib/system.cmx ide/preferences.cmx lib/pp.cmx ide/minilib.cmx \
    lib/feedback.cmx lib/envars.cmx config/coq_config.cmx clib/cList.cmx \
    ide/ideutils.cmi
ide/ideutils.cmi : ide/protocol/richpp.cmi lib/pp.cmi lib/feedback.cmi
ide/macos_prehook.cmo : ide/macos_prehook.cmi
ide/macos_prehook.cmx : ide/macos_prehook.cmi
ide/macos_prehook.cmi :
ide/minilib.cmo : lib/pp.cmi lib/envars.cmi ide/minilib.cmi
ide/minilib.cmx : lib/pp.cmx lib/envars.cmx ide/minilib.cmi
ide/minilib.cmi : lib/pp.cmi
ide/nanoPG.cmo : ide/wg_Notebook.cmi ide/session.cmi ide/preferences.cmi \
    clib/option.cmi ide/ideutils.cmi lib/flags.cmi ide/nanoPG.cmi
ide/nanoPG.cmx : ide/wg_Notebook.cmx ide/session.cmx ide/preferences.cmx \
    clib/option.cmx ide/ideutils.cmx lib/flags.cmx ide/nanoPG.cmi
ide/nanoPG.cmi : ide/wg_Notebook.cmi ide/session.cmi
ide/preferences.cmo : lib/util.cmi ide/tags.cmi clib/option.cmi \
    ide/minilib.cmi clib/int.cmi lib/flags.cmi lib/envars.cmi \
    config/coq_config.cmi ide/configwin.cmi ide/config_lexer.cmi \
    clib/cString.cmi clib/cList.cmi ide/preferences.cmi
ide/preferences.cmx : lib/util.cmx ide/tags.cmx clib/option.cmx \
    ide/minilib.cmx clib/int.cmx lib/flags.cmx lib/envars.cmx \
    config/coq_config.cmx ide/configwin.cmx ide/config_lexer.cmx \
    clib/cString.cmx clib/cList.cmx ide/preferences.cmi
ide/preferences.cmi : lib/util.cmi
ide/protocol/interface.cmo : lib/xml_datatype.cmi lib/util.cmi \
    lib/stateid.cmi lib/pp.cmi lib/feedback.cmi clib/exninfo.cmi
ide/protocol/interface.cmx : lib/xml_datatype.cmi lib/util.cmx \
    lib/stateid.cmx lib/pp.cmx lib/feedback.cmx clib/exninfo.cmx
ide/protocol/richpp.cmo : lib/xml_datatype.cmi lib/util.cmi lib/pp.cmi \
    ide/protocol/richpp.cmi
ide/protocol/richpp.cmx : lib/xml_datatype.cmi lib/util.cmx lib/pp.cmx \
    ide/protocol/richpp.cmi
ide/protocol/richpp.cmi : lib/xml_datatype.cmi lib/pp.cmi
ide/protocol/serialize.cmo : lib/xml_datatype.cmi lib/loc.cmi \
    clib/cString.cmi clib/cSig.cmi ide/protocol/serialize.cmi
ide/protocol/serialize.cmx : lib/xml_datatype.cmi lib/loc.cmx \
    clib/cString.cmx clib/cSig.cmi ide/protocol/serialize.cmi
ide/protocol/serialize.cmi : lib/xml_datatype.cmi lib/loc.cmi clib/cSig.cmi
ide/protocol/xml_lexer.cmo : ide/protocol/xml_lexer.cmi
ide/protocol/xml_lexer.cmx : ide/protocol/xml_lexer.cmi
ide/protocol/xml_lexer.cmi :
ide/protocol/xml_parser.cmo : ide/protocol/xml_lexer.cmi \
    lib/xml_datatype.cmi ide/protocol/xml_parser.cmi
ide/protocol/xml_parser.cmx : ide/protocol/xml_lexer.cmx \
    lib/xml_datatype.cmi ide/protocol/xml_parser.cmi
ide/protocol/xml_parser.cmi : lib/xml_datatype.cmi
ide/protocol/xml_printer.cmo : lib/xml_datatype.cmi \
    ide/protocol/xml_printer.cmi
ide/protocol/xml_printer.cmx : lib/xml_datatype.cmi \
    ide/protocol/xml_printer.cmi
ide/protocol/xml_printer.cmi : lib/xml_datatype.cmi
ide/protocol/xmlprotocol.cmo : ide/protocol/xml_printer.cmi \
    lib/xml_datatype.cmi lib/util.cmi lib/stateid.cmi \
    ide/protocol/serialize.cmi ide/protocol/richpp.cmi lib/pp.cmi \
    ide/protocol/interface.cmo lib/feedback.cmi clib/cSig.cmi lib/cErrors.cmi \
    ide/protocol/xmlprotocol.cmi
ide/protocol/xmlprotocol.cmx : ide/protocol/xml_printer.cmx \
    lib/xml_datatype.cmi lib/util.cmx lib/stateid.cmx \
    ide/protocol/serialize.cmx ide/protocol/richpp.cmx lib/pp.cmx \
    ide/protocol/interface.cmx lib/feedback.cmx clib/cSig.cmi lib/cErrors.cmx \
    ide/protocol/xmlprotocol.cmi
ide/protocol/xmlprotocol.cmi : lib/xml_datatype.cmi \
    ide/protocol/interface.cmo lib/feedback.cmi
ide/sentence.cmo : ide/tags.cmi ide/coq_lex.cmi ide/sentence.cmi
ide/sentence.cmx : ide/tags.cmx ide/coq_lex.cmx ide/sentence.cmi
ide/sentence.cmi :
ide/session.cmo : ide/wg_Segment.cmi ide/wg_ScriptView.cmi \
    ide/wg_RoutedMessageViews.cmi ide/wg_ProofView.cmi ide/wg_MessageView.cmi \
    ide/wg_Find.cmi ide/wg_Detachable.cmi ide/wg_Command.cmi ide/tags.cmi \
    ide/sentence.cmi ide/preferences.cmi ide/minilib.cmi ide/ideutils.cmi \
    ide/fileOps.cmi ide/coqOps.cmi ide/coq.cmi clib/cString.cmi \
    clib/cList.cmi ide/session.cmi
ide/session.cmx : ide/wg_Segment.cmx ide/wg_ScriptView.cmx \
    ide/wg_RoutedMessageViews.cmx ide/wg_ProofView.cmx ide/wg_MessageView.cmx \
    ide/wg_Find.cmx ide/wg_Detachable.cmx ide/wg_Command.cmx ide/tags.cmx \
    ide/sentence.cmx ide/preferences.cmx ide/minilib.cmx ide/ideutils.cmx \
    ide/fileOps.cmx ide/coqOps.cmx ide/coq.cmx clib/cString.cmx \
    clib/cList.cmx ide/session.cmi
ide/session.cmi : ide/wg_Segment.cmi ide/wg_ScriptView.cmi \
    ide/wg_RoutedMessageViews.cmi ide/wg_ProofView.cmi ide/wg_Find.cmi \
    ide/wg_Command.cmi ide/fileOps.cmi ide/coqOps.cmi ide/coq.cmi \
    clib/cString.cmi
ide/tags.cmo : ide/tags.cmi
ide/tags.cmx : ide/tags.cmi
ide/tags.cmi :
ide/utf8_convert.cmo : ide/utf8_convert.cmi
ide/utf8_convert.cmx : ide/utf8_convert.cmi
ide/utf8_convert.cmi :
ide/wg_Command.cmo : ide/wg_MessageView.cmi ide/wg_Detachable.cmi \
    ide/tags.cmi ide/preferences.cmi lib/pp.cmi ide/protocol/interface.cmo \
    ide/ideutils.cmi ide/coq_commands.cmi ide/coq.cmi ide/wg_Command.cmi
ide/wg_Command.cmx : ide/wg_MessageView.cmx ide/wg_Detachable.cmx \
    ide/tags.cmx ide/preferences.cmx lib/pp.cmx ide/protocol/interface.cmx \
    ide/ideutils.cmx ide/coq_commands.cmx ide/coq.cmx ide/wg_Command.cmi
ide/wg_Command.cmi : ide/wg_RoutedMessageViews.cmi ide/coqOps.cmi \
    ide/coq.cmi
ide/wg_Completion.cmo : ide/preferences.cmi ide/minilib.cmi \
    ide/protocol/interface.cmo ide/gtk_parsing.cmi ide/coq.cmi \
    ide/wg_Completion.cmi
ide/wg_Completion.cmx : ide/preferences.cmx ide/minilib.cmx \
    ide/protocol/interface.cmx ide/gtk_parsing.cmx ide/coq.cmx \
    ide/wg_Completion.cmi
ide/wg_Completion.cmi : ide/coq.cmi
ide/wg_Detachable.cmo : clib/option.cmi ide/wg_Detachable.cmi
ide/wg_Detachable.cmx : clib/option.cmx ide/wg_Detachable.cmi
ide/wg_Detachable.cmi :
ide/wg_Find.cmo : ide/wg_Detachable.cmi lib/pp.cmi clib/int.cmi \
    ide/ideutils.cmi clib/cString.cmi lib/cErrors.cmi ide/wg_Find.cmi
ide/wg_Find.cmx : ide/wg_Detachable.cmx lib/pp.cmx clib/int.cmx \
    ide/ideutils.cmx clib/cString.cmx lib/cErrors.cmx ide/wg_Find.cmi
ide/wg_Find.cmi :
ide/wg_MessageView.cmo : ide/tags.cmi ide/protocol/richpp.cmi \
    ide/preferences.cmi lib/pp.cmi ide/ideutils.cmi ide/gtk_parsing.cmi \
    lib/feedback.cmi ide/wg_MessageView.cmi
ide/wg_MessageView.cmx : ide/tags.cmx ide/protocol/richpp.cmx \
    ide/preferences.cmx lib/pp.cmx ide/ideutils.cmx ide/gtk_parsing.cmx \
    lib/feedback.cmx ide/wg_MessageView.cmi
ide/wg_MessageView.cmi : lib/pp.cmi ide/ideutils.cmi
ide/wg_Notebook.cmo : lib/util.cmi ide/wg_Notebook.cmi
ide/wg_Notebook.cmx : lib/util.cmx ide/wg_Notebook.cmi
ide/wg_Notebook.cmi :
ide/wg_ProofView.cmo : lib/util.cmi ide/tags.cmi ide/protocol/richpp.cmi \
    ide/preferences.cmi ide/protocol/interface.cmo ide/ideutils.cmi \
    ide/gtk_parsing.cmi ide/coq.cmi ide/wg_ProofView.cmi
ide/wg_ProofView.cmx : lib/util.cmx ide/tags.cmx ide/protocol/richpp.cmx \
    ide/preferences.cmx ide/protocol/interface.cmx ide/ideutils.cmx \
    ide/gtk_parsing.cmx ide/coq.cmx ide/wg_ProofView.cmi
ide/wg_ProofView.cmi : ide/protocol/interface.cmo
ide/wg_RoutedMessageViews.cmo : ide/wg_MessageView.cmi clib/option.cmi \
    ide/wg_RoutedMessageViews.cmi
ide/wg_RoutedMessageViews.cmx : ide/wg_MessageView.cmx clib/option.cmx \
    ide/wg_RoutedMessageViews.cmi
ide/wg_RoutedMessageViews.cmi : ide/wg_MessageView.cmi
ide/wg_ScriptView.cmo : ide/wg_Completion.cmi ide/preferences.cmi \
    ide/minilib.cmi ide/gtk_parsing.cmi ide/coq.cmi ide/wg_ScriptView.cmi
ide/wg_ScriptView.cmx : ide/wg_Completion.cmx ide/preferences.cmx \
    ide/minilib.cmx ide/gtk_parsing.cmx ide/coq.cmx ide/wg_ScriptView.cmi
ide/wg_ScriptView.cmi : ide/wg_Completion.cmi ide/coq.cmi
ide/wg_Segment.cmo : lib/util.cmi ide/preferences.cmi ide/ideutils.cmi \
    ide/wg_Segment.cmi
ide/wg_Segment.cmx : lib/util.cmx ide/preferences.cmx ide/ideutils.cmx \
    ide/wg_Segment.cmi
ide/wg_Segment.cmi :
interp/constrexpr.cmo : engine/uState.cmi pretyping/pattern.cmo \
    kernel/names.cmi engine/namegen.cmi library/libnames.cmi \
    pretyping/glob_term.cmo lib/genarg.cmi engine/evar_kinds.cmi \
    library/decl_kinds.cmo kernel/constr.cmi lib/cAst.cmi
interp/constrexpr.cmx : engine/uState.cmx pretyping/pattern.cmx \
    kernel/names.cmx engine/namegen.cmx library/libnames.cmx \
    pretyping/glob_term.cmx lib/genarg.cmx engine/evar_kinds.cmx \
    library/decl_kinds.cmx kernel/constr.cmx lib/cAst.cmx
interp/constrexpr_ops.cmo : lib/util.cmi kernel/univ.cmi engine/uState.cmi \
    engine/termops.cmi interp/smartlocate.cmi pretyping/pretyping.cmi \
    lib/pp.cmi clib/option.cmi interp/notation.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi lib/loc.cmi \
    library/libnames.cmi clib/int.cmi library/goptions.cmi \
    library/globnames.cmi pretyping/glob_term.cmo pretyping/glob_ops.cmi \
    lib/feedback.cmi engine/evd.cmi kernel/environ.cmi library/decl_kinds.cmo \
    interp/constrexpr.cmo lib/cErrors.cmi lib/cAst.cmi \
    interp/constrexpr_ops.cmi
interp/constrexpr_ops.cmx : lib/util.cmx kernel/univ.cmx engine/uState.cmx \
    engine/termops.cmx interp/smartlocate.cmx pretyping/pretyping.cmx \
    lib/pp.cmx clib/option.cmx interp/notation.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx lib/loc.cmx \
    library/libnames.cmx clib/int.cmx library/goptions.cmx \
    library/globnames.cmx pretyping/glob_term.cmx pretyping/glob_ops.cmx \
    lib/feedback.cmx engine/evd.cmx kernel/environ.cmx library/decl_kinds.cmx \
    interp/constrexpr.cmx lib/cErrors.cmx lib/cAst.cmx \
    interp/constrexpr_ops.cmi
interp/constrexpr_ops.cmi : engine/uState.cmi kernel/names.cmi lib/loc.cmi \
    library/libnames.cmi pretyping/glob_term.cmo engine/evd.cmi \
    kernel/environ.cmi library/decl_kinds.cmo interp/constrexpr.cmo
interp/constrextern.cmo : lib/util.cmi engine/termops.cmi \
    library/summary.cmi pretyping/recordops.cmi lib/pp.cmi \
    pretyping/patternops.cmi pretyping/pattern.cmo clib/option.cmi \
    interp/notation_ops.cmi interp/notation.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    library/libnames.cmi clib/int.cmi pretyping/inductiveops.cmi \
    interp/impargs.cmi library/goptions.cmi library/globnames.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi engine/evar_kinds.cmi \
    pretyping/detyping.cmi library/decl_kinds.cmo lib/dAst.cmi \
    kernel/context.cmi interp/constrintern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo kernel/constr.cmi pretyping/classops.cmi \
    clib/cString.cmi lib/cErrors.cmi lib/cAst.cmi interp/constrextern.cmi
interp/constrextern.cmx : lib/util.cmx engine/termops.cmx \
    library/summary.cmx pretyping/recordops.cmx lib/pp.cmx \
    pretyping/patternops.cmx pretyping/pattern.cmx clib/option.cmx \
    interp/notation_ops.cmx interp/notation.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    library/libnames.cmx clib/int.cmx pretyping/inductiveops.cmx \
    interp/impargs.cmx library/goptions.cmx library/globnames.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evar_kinds.cmx \
    pretyping/detyping.cmx library/decl_kinds.cmx lib/dAst.cmx \
    kernel/context.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx kernel/constr.cmx pretyping/classops.cmx \
    clib/cString.cmx lib/cErrors.cmx lib/cAst.cmx interp/constrextern.cmi
interp/constrextern.cmi : engine/termops.cmi kernel/sorts.cmi \
    pretyping/pattern.cmo interp/notation_term.cmo interp/notation.cmi \
    kernel/names.cmi pretyping/ltac_pretype.cmo lib/loc.cmi \
    library/libnames.cmi pretyping/glob_term.cmo engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi interp/constrexpr.cmo
interp/constrintern.cmo : lib/util.cmi engine/termops.cmi kernel/term.cmi \
    interp/syntax_def.cmi interp/smartlocate.cmi interp/reserve.cmi \
    pretyping/recordops.cmi pretyping/program.cmi pretyping/pretyping.cmi \
    lib/pp.cmi pretyping/patternops.cmi clib/option.cmi \
    interp/notation_term.cmo interp/notation_ops.cmi interp/notation.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi lib/loc.cmi library/libnames.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi \
    interp/implicit_quantifiers.cmi interp/impargs.cmi library/globnames.cmi \
    library/global.cmi pretyping/glob_term.cmo pretyping/glob_ops.cmi \
    interp/genintern.cmi engine/evar_kinds.cmi kernel/environ.cmi \
    engine/eConstr.cmi interp/dumpglob.cmi library/decls.cmi \
    kernel/declarations.cmo library/decl_kinds.cmo lib/dAst.cmi \
    kernel/context.cmi interp/constrexpr_ops.cmi interp/constrexpr.cmo \
    kernel/constr.cmi pretyping/cases.cmi clib/cList.cmi lib/cErrors.cmi \
    lib/cAst.cmi interp/constrintern.cmi
interp/constrintern.cmx : lib/util.cmx engine/termops.cmx kernel/term.cmx \
    interp/syntax_def.cmx interp/smartlocate.cmx interp/reserve.cmx \
    pretyping/recordops.cmx pretyping/program.cmx pretyping/pretyping.cmx \
    lib/pp.cmx pretyping/patternops.cmx clib/option.cmx \
    interp/notation_term.cmx interp/notation_ops.cmx interp/notation.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx lib/loc.cmx library/libnames.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx \
    interp/implicit_quantifiers.cmx interp/impargs.cmx library/globnames.cmx \
    library/global.cmx pretyping/glob_term.cmx pretyping/glob_ops.cmx \
    interp/genintern.cmx engine/evar_kinds.cmx kernel/environ.cmx \
    engine/eConstr.cmx interp/dumpglob.cmx library/decls.cmx \
    kernel/declarations.cmx library/decl_kinds.cmx lib/dAst.cmx \
    kernel/context.cmx interp/constrexpr_ops.cmx interp/constrexpr.cmx \
    kernel/constr.cmx pretyping/cases.cmx clib/cList.cmx lib/cErrors.cmx \
    lib/cAst.cmx interp/constrintern.cmi
interp/constrintern.cmi : pretyping/pretyping.cmi pretyping/pattern.cmo \
    interp/notation_term.cmo kernel/names.cmi library/libnames.cmi \
    interp/impargs.cmi pretyping/glob_term.cmo interp/genintern.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    interp/constrexpr.cmo
interp/declare.cmo : kernel/vars.cmi lib/util.cmi engine/univNames.cmi \
    engine/univGen.cmi kernel/univ.cmi kernel/safe_typing.cmi \
    pretyping/recordops.cmi pretyping/pretyping.cmi lib/pp.cmi \
    clib/option.cmi kernel/opaqueproof.cmi interp/notation.cmi \
    library/nametab.cmi kernel/names.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi pretyping/inferCumulativity.cmi \
    pretyping/inductiveops.cmi interp/impargs.cmi pretyping/heads.cmi \
    library/globnames.cmi library/global.cmi lib/future.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi kernel/environ.cmi kernel/entries.cmo \
    library/dischargedhypsmap.cmi interp/discharge.cmi library/decls.cmi \
    kernel/declareops.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    kernel/cooking.cmi kernel/constr.cmi lib/cErrors.cmi lib/cAst.cmi \
    interp/declare.cmi
interp/declare.cmx : kernel/vars.cmx lib/util.cmx engine/univNames.cmx \
    engine/univGen.cmx kernel/univ.cmx kernel/safe_typing.cmx \
    pretyping/recordops.cmx pretyping/pretyping.cmx lib/pp.cmx \
    clib/option.cmx kernel/opaqueproof.cmx interp/notation.cmx \
    library/nametab.cmx kernel/names.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx pretyping/inferCumulativity.cmx \
    pretyping/inductiveops.cmx interp/impargs.cmx pretyping/heads.cmx \
    library/globnames.cmx library/global.cmx lib/future.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx kernel/environ.cmx kernel/entries.cmx \
    library/dischargedhypsmap.cmx interp/discharge.cmx library/decls.cmx \
    kernel/declareops.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    kernel/cooking.cmx kernel/constr.cmx lib/cErrors.cmx lib/cAst.cmx \
    interp/declare.cmi
interp/declare.cmi : engine/univNames.cmi kernel/univ.cmi \
    kernel/safe_typing.cmi kernel/names.cmi library/libnames.cmi \
    pretyping/glob_term.cmo lib/future.cmi kernel/entries.cmo \
    library/decl_kinds.cmo kernel/constr.cmi
interp/discharge.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    engine/termops.cmi kernel/term.cmi lib/pp.cmi kernel/names.cmi \
    library/lib.cmi kernel/entries.cmo kernel/declarations.cmo \
    kernel/cooking.cmi kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    interp/discharge.cmi
interp/discharge.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    engine/termops.cmx kernel/term.cmx lib/pp.cmx kernel/names.cmx \
    library/lib.cmx kernel/entries.cmx kernel/declarations.cmx \
    kernel/cooking.cmx kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    interp/discharge.cmi
interp/discharge.cmi : kernel/opaqueproof.cmi library/lib.cmi \
    kernel/entries.cmo kernel/declarations.cmo
interp/dumpglob.cmo : lib/util.cmi pretyping/typeclasses.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi lib/loc.cmi library/libnames.cmi \
    library/lib.cmi clib/int.cmi kernel/inductive.cmi library/globnames.cmi \
    library/global.cmi lib/feedback.cmi library/decls.cmi \
    kernel/declarations.cmo library/decl_kinds.cmo interp/constrexpr.cmo \
    lib/cAst.cmi interp/dumpglob.cmi
interp/dumpglob.cmx : lib/util.cmx pretyping/typeclasses.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx lib/loc.cmx library/libnames.cmx \
    library/lib.cmx clib/int.cmx kernel/inductive.cmx library/globnames.cmx \
    library/global.cmx lib/feedback.cmx library/decls.cmx \
    kernel/declarations.cmx library/decl_kinds.cmx interp/constrexpr.cmx \
    lib/cAst.cmx interp/dumpglob.cmi
interp/dumpglob.cmi : interp/notation_term.cmo interp/notation.cmi \
    kernel/names.cmi lib/loc.cmi interp/constrexpr.cmo
interp/genintern.cmo : clib/store.cmi pretyping/pattern.cmo kernel/names.cmi \
    kernel/mod_subst.cmi lib/hook.cmi pretyping/glob_term.cmo lib/genarg.cmi \
    kernel/environ.cmi pretyping/detyping.cmi interp/constrexpr.cmo \
    interp/genintern.cmi
interp/genintern.cmx : clib/store.cmx pretyping/pattern.cmx kernel/names.cmx \
    kernel/mod_subst.cmx lib/hook.cmx pretyping/glob_term.cmx lib/genarg.cmx \
    kernel/environ.cmx pretyping/detyping.cmx interp/constrexpr.cmx \
    interp/genintern.cmi
interp/genintern.cmi : clib/store.cmi pretyping/pattern.cmo kernel/names.cmi \
    kernel/mod_subst.cmi pretyping/glob_term.cmo lib/genarg.cmi \
    kernel/environ.cmi interp/constrexpr.cmo
interp/genredexpr.cmo : lib/util.cmi kernel/names.cmi pretyping/locus.cmo \
    library/libnames.cmi interp/constrexpr.cmo
interp/genredexpr.cmx : lib/util.cmx kernel/names.cmx pretyping/locus.cmx \
    library/libnames.cmx interp/constrexpr.cmx
interp/impargs.cmo : kernel/vars.cmi lib/util.cmi engine/termops.cmi \
    library/summary.cmi pretyping/reductionops.cmi lib/pp.cmi clib/option.cmi \
    kernel/names.cmi engine/namegen.cmi library/libobject.cmi library/lib.cmi \
    clib/int.cmi library/globnames.cmi library/global.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/declarations.cmo \
    library/decl_kinds.cmo kernel/context.cmi interp/constrexpr.cmo \
    kernel/constr.cmi clib/cList.cmi lib/cErrors.cmi \
    pretyping/arguments_renaming.cmi interp/impargs.cmi
interp/impargs.cmx : kernel/vars.cmx lib/util.cmx engine/termops.cmx \
    library/summary.cmx pretyping/reductionops.cmx lib/pp.cmx clib/option.cmx \
    kernel/names.cmx engine/namegen.cmx library/libobject.cmx library/lib.cmx \
    clib/int.cmx library/globnames.cmx library/global.cmx engine/evd.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/declarations.cmx \
    library/decl_kinds.cmx kernel/context.cmx interp/constrexpr.cmx \
    kernel/constr.cmx clib/cList.cmx lib/cErrors.cmx \
    pretyping/arguments_renaming.cmx interp/impargs.cmi
interp/impargs.cmi : kernel/names.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi interp/constrexpr.cmo
interp/implicit_quantifiers.cmo : lib/util.cmi \
    pretyping/typeclasses_errors.cmi pretyping/typeclasses.cmi \
    library/summary.cmi lib/pp.cmi clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi clib/int.cmi library/global.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi kernel/environ.cmi \
    library/decl_kinds.cmo lib/dAst.cmi kernel/context.cmi \
    interp/constrexpr_ops.cmi interp/constrexpr.cmo kernel/constr.cmi \
    lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    interp/implicit_quantifiers.cmi
interp/implicit_quantifiers.cmx : lib/util.cmx \
    pretyping/typeclasses_errors.cmx pretyping/typeclasses.cmx \
    library/summary.cmx lib/pp.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx library/global.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx kernel/environ.cmx \
    library/decl_kinds.cmx lib/dAst.cmx kernel/context.cmx \
    interp/constrexpr_ops.cmx interp/constrexpr.cmx kernel/constr.cmx \
    lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    interp/implicit_quantifiers.cmi
interp/implicit_quantifiers.cmi : pretyping/typeclasses_errors.cmi \
    kernel/names.cmi library/libnames.cmi interp/impargs.cmi \
    pretyping/glob_term.cmo kernel/environ.cmi interp/constrexpr.cmo \
    kernel/constr.cmi lib/cAst.cmi
interp/modintern.cmo : kernel/univ.cmi engine/uState.cmi library/nametab.cmi \
    kernel/modops.cmi lib/loc.cmi library/libnames.cmi lib/flags.cmi \
    kernel/entries.cmo engine/eConstr.cmi interp/dumpglob.cmi \
    library/declaremods.cmi kernel/declarations.cmo interp/constrintern.cmi \
    interp/constrexpr_ops.cmi interp/constrexpr.cmo lib/cAst.cmi \
    interp/modintern.cmi
interp/modintern.cmx : kernel/univ.cmx engine/uState.cmx library/nametab.cmx \
    kernel/modops.cmx lib/loc.cmx library/libnames.cmx lib/flags.cmx \
    kernel/entries.cmx engine/eConstr.cmx interp/dumpglob.cmx \
    library/declaremods.cmx kernel/declarations.cmx interp/constrintern.cmx \
    interp/constrexpr_ops.cmx interp/constrexpr.cmx lib/cAst.cmx \
    interp/modintern.cmi
interp/modintern.cmi : kernel/univ.cmi kernel/environ.cmi kernel/entries.cmo \
    library/declaremods.cmi interp/constrexpr.cmo
interp/notation.cmo : pretyping/vnorm.cmi lib/util.cmi clib/unicode.cmi \
    pretyping/typing.cmi kernel/type_errors.cmi engine/termops.cmi \
    library/summary.cmi pretyping/reductionops.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi clib/option.cmi \
    interp/notation_term.cmo interp/notation_ops.cmi library/nametab.cmi \
    kernel/names.cmi lib/loc.cmi library/libobject.cmi library/libnames.cmi \
    library/lib.cmi clib/int.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    lib/dAst.cmi kernel/context.cmi interp/constrexpr.cmo kernel/constr.cmi \
    pretyping/classops.cmi lib/cWarnings.cmi clib/cMap.cmi lib/cErrors.cmi \
    clib/bigint.cmi interp/notation.cmi
interp/notation.cmx : pretyping/vnorm.cmx lib/util.cmx clib/unicode.cmx \
    pretyping/typing.cmx kernel/type_errors.cmx engine/termops.cmx \
    library/summary.cmx pretyping/reductionops.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx clib/option.cmx \
    interp/notation_term.cmx interp/notation_ops.cmx library/nametab.cmx \
    kernel/names.cmx lib/loc.cmx library/libobject.cmx library/libnames.cmx \
    library/lib.cmx clib/int.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    lib/dAst.cmx kernel/context.cmx interp/constrexpr.cmx kernel/constr.cmx \
    pretyping/classops.cmx lib/cWarnings.cmx clib/cMap.cmx lib/cErrors.cmx \
    clib/bigint.cmx interp/notation.cmi
interp/notation.cmi : lib/pp.cmi interp/notation_term.cmo kernel/names.cmi \
    kernel/mod_subst.cmi lib/loc.cmi library/libnames.cmi \
    pretyping/glob_term.cmo engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi interp/constrexpr.cmo kernel/constr.cmi \
    pretyping/classops.cmi clib/cMap.cmi clib/bigint.cmi
interp/notation_ops.cmo : lib/util.cmi lib/pp.cmi clib/option.cmi \
    interp/notation_term.cmo kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi kernel/mod_subst.cmi lib/loc.cmi clib/int.cmi \
    pretyping/inductiveops.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi interp/genintern.cmi \
    engine/evd.cmi engine/evar_kinds.cmi engine/eConstr.cmi \
    pretyping/detyping.cmi library/decl_kinds.cmo lib/dAst.cmi \
    interp/constrexpr.cmo kernel/constr.cmi lib/cErrors.cmi lib/cAst.cmi \
    interp/notation_ops.cmi
interp/notation_ops.cmx : lib/util.cmx lib/pp.cmx clib/option.cmx \
    interp/notation_term.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx kernel/mod_subst.cmx lib/loc.cmx clib/int.cmx \
    pretyping/inductiveops.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx interp/genintern.cmx \
    engine/evd.cmx engine/evar_kinds.cmx engine/eConstr.cmx \
    pretyping/detyping.cmx library/decl_kinds.cmx lib/dAst.cmx \
    interp/constrexpr.cmx kernel/constr.cmx lib/cErrors.cmx lib/cAst.cmx \
    interp/notation_ops.cmi
interp/notation_ops.cmi : interp/notation_term.cmo kernel/names.cmi \
    kernel/mod_subst.cmi lib/loc.cmi pretyping/glob_term.cmo
interp/notation_term.cmo : kernel/names.cmi engine/namegen.cmi \
    pretyping/glob_term.cmo lib/genarg.cmi engine/evar_kinds.cmi \
    interp/constrexpr.cmo kernel/constr.cmi
interp/notation_term.cmx : kernel/names.cmx engine/namegen.cmx \
    pretyping/glob_term.cmx lib/genarg.cmx engine/evar_kinds.cmx \
    interp/constrexpr.cmx kernel/constr.cmx
interp/redops.cmo : lib/util.cmi lib/pp.cmi clib/option.cmi \
    interp/genredexpr.cmo lib/cErrors.cmi interp/redops.cmi
interp/redops.cmx : lib/util.cmx lib/pp.cmx clib/option.cmx \
    interp/genredexpr.cmx lib/cErrors.cmx interp/redops.cmi
interp/redops.cmi : interp/genredexpr.cmo
interp/reserve.cmo : lib/util.cmi library/summary.cmi lib/pp.cmi \
    interp/notation_term.cmo interp/notation_ops.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi library/libobject.cmi \
    library/lib.cmi library/globnames.cmi library/global.cmi engine/evd.cmi \
    engine/eConstr.cmi pretyping/detyping.cmi kernel/constr.cmi \
    lib/cErrors.cmi lib/cAst.cmi interp/reserve.cmi
interp/reserve.cmx : lib/util.cmx library/summary.cmx lib/pp.cmx \
    interp/notation_term.cmx interp/notation_ops.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx library/libobject.cmx \
    library/lib.cmx library/globnames.cmx library/global.cmx engine/evd.cmx \
    engine/eConstr.cmx pretyping/detyping.cmx kernel/constr.cmx \
    lib/cErrors.cmx lib/cAst.cmx interp/reserve.cmi
interp/reserve.cmi : interp/notation_term.cmo kernel/names.cmi
interp/smartlocate.cmo : interp/syntax_def.cmi lib/pp.cmi \
    interp/notation_term.cmo interp/notation.cmi library/nametab.cmi \
    library/libnames.cmi library/globnames.cmi interp/constrexpr.cmo \
    lib/cErrors.cmi lib/cAst.cmi interp/smartlocate.cmi
interp/smartlocate.cmx : interp/syntax_def.cmx lib/pp.cmx \
    interp/notation_term.cmx interp/notation.cmx library/nametab.cmx \
    library/libnames.cmx library/globnames.cmx interp/constrexpr.cmx \
    lib/cErrors.cmx lib/cAst.cmx interp/smartlocate.cmi
interp/smartlocate.cmi : kernel/names.cmi library/libnames.cmi \
    library/globnames.cmi interp/constrexpr.cmo
interp/stdarg.cmo : kernel/names.cmi pretyping/geninterp.cmi lib/genarg.cmi \
    interp/stdarg.cmi
interp/stdarg.cmx : kernel/names.cmx pretyping/geninterp.cmx lib/genarg.cmx \
    interp/stdarg.cmi
interp/stdarg.cmi : kernel/sorts.cmi pretyping/pattern.cmo kernel/names.cmi \
    pretyping/ltac_pretype.cmo pretyping/locus.cmo lib/loc.cmi \
    library/libnames.cmi interp/genredexpr.cmo interp/genintern.cmi \
    lib/genarg.cmi engine/eConstr.cmi interp/constrexpr.cmo
interp/syntax_def.cmo : lib/util.cmi library/summary.cmi lib/pp.cmi \
    interp/notation_term.cmo interp/notation_ops.cmi interp/notation.cmi \
    library/nametab.cmi kernel/names.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi clib/int.cmi lib/flags.cmi \
    interp/constrexpr.cmo lib/cWarnings.cmi lib/cErrors.cmi \
    interp/syntax_def.cmi
interp/syntax_def.cmx : lib/util.cmx library/summary.cmx lib/pp.cmx \
    interp/notation_term.cmx interp/notation_ops.cmx interp/notation.cmx \
    library/nametab.cmx kernel/names.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx lib/flags.cmx \
    interp/constrexpr.cmx lib/cWarnings.cmx lib/cErrors.cmx \
    interp/syntax_def.cmi
interp/syntax_def.cmi : interp/notation_term.cmo kernel/names.cmi \
    lib/loc.cmi lib/flags.cmi
kernel/cClosure.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/term.cmi clib/range.cmi lib/pp.cmi kernel/names.cmi clib/int.cmi \
    clib/hashset.cmi lib/feedback.cmi kernel/esubst.cmi kernel/environ.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi clib/cArray.cmi kernel/cClosure.cmi
kernel/cClosure.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/term.cmx clib/range.cmx lib/pp.cmx kernel/names.cmx clib/int.cmx \
    clib/hashset.cmx lib/feedback.cmx kernel/esubst.cmx kernel/environ.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx clib/cArray.cmx kernel/cClosure.cmi
kernel/cClosure.cmi : kernel/univ.cmi kernel/names.cmi kernel/esubst.cmi \
    kernel/environ.cmi kernel/conv_oracle.cmi kernel/constr.cmi
kernel/cPrimitives.cmo : kernel/cPrimitives.cmi
kernel/cPrimitives.cmx : kernel/cPrimitives.cmi
kernel/cPrimitives.cmi :
kernel/cbytecodes.cmo : kernel/vmvalues.cmi lib/util.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi kernel/evar.cmi kernel/cbytecodes.cmi
kernel/cbytecodes.cmx : kernel/vmvalues.cmx lib/util.cmx lib/pp.cmx \
    kernel/names.cmx clib/int.cmx kernel/evar.cmx kernel/cbytecodes.cmi
kernel/cbytecodes.cmi : kernel/vmvalues.cmi lib/pp.cmi kernel/names.cmi \
    kernel/evar.cmi
kernel/cbytegen.cmo : kernel/vmvalues.cmi lib/util.cmi kernel/univ.cmi \
    kernel/uint31.cmi kernel/sorts.cmi lib/pp.cmi clib/option.cmi \
    kernel/names.cmi kernel/mod_subst.cmi clib/int.cmi lib/feedback.cmi \
    kernel/environ.cmi kernel/declarations.cmo kernel/constr.cmi \
    kernel/clambda.cmi kernel/cinstr.cmi kernel/cemitcodes.cmi \
    kernel/cbytecodes.cmi lib/cErrors.cmi kernel/cbytegen.cmi
kernel/cbytegen.cmx : kernel/vmvalues.cmx lib/util.cmx kernel/univ.cmx \
    kernel/uint31.cmx kernel/sorts.cmx lib/pp.cmx clib/option.cmx \
    kernel/names.cmx kernel/mod_subst.cmx clib/int.cmx lib/feedback.cmx \
    kernel/environ.cmx kernel/declarations.cmx kernel/constr.cmx \
    kernel/clambda.cmx kernel/cinstr.cmi kernel/cemitcodes.cmx \
    kernel/cbytecodes.cmx lib/cErrors.cmx kernel/cbytegen.cmi
kernel/cbytegen.cmi : kernel/names.cmi kernel/environ.cmi \
    kernel/declarations.cmo kernel/constr.cmi kernel/cemitcodes.cmi \
    kernel/cbytecodes.cmi
kernel/cemitcodes.cmo : kernel/vmvalues.cmi kernel/names.cmi \
    kernel/mod_subst.cmi clib/int.cmi clib/hashset.cmi kernel/copcodes.cmo \
    kernel/constr.cmi kernel/cbytecodes.cmi clib/cString.cmi clib/cArray.cmi \
    kernel/cemitcodes.cmi
kernel/cemitcodes.cmx : kernel/vmvalues.cmx kernel/names.cmx \
    kernel/mod_subst.cmx clib/int.cmx clib/hashset.cmx kernel/copcodes.cmx \
    kernel/constr.cmx kernel/cbytecodes.cmx clib/cString.cmx clib/cArray.cmx \
    kernel/cemitcodes.cmi
kernel/cemitcodes.cmi : kernel/vmvalues.cmi kernel/names.cmi \
    kernel/mod_subst.cmi kernel/cbytecodes.cmi
kernel/cinstr.cmi : kernel/vmvalues.cmi kernel/uint31.cmi kernel/sorts.cmi \
    kernel/names.cmi kernel/evar.cmi kernel/constr.cmi kernel/cbytecodes.cmi
kernel/clambda.cmo : kernel/vmvalues.cmi lib/util.cmi kernel/uint31.cmi \
    kernel/term.cmi kernel/sorts.cmi kernel/retroknowledge.cmi \
    kernel/reduction.cmi lib/pp.cmi kernel/names.cmi kernel/mod_subst.cmi \
    clib/int.cmi lib/feedback.cmi kernel/evar.cmi kernel/esubst.cmi \
    kernel/environ.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi kernel/cinstr.cmi kernel/cemitcodes.cmi \
    kernel/cbytecodes.cmi kernel/clambda.cmi
kernel/clambda.cmx : kernel/vmvalues.cmx lib/util.cmx kernel/uint31.cmx \
    kernel/term.cmx kernel/sorts.cmx kernel/retroknowledge.cmx \
    kernel/reduction.cmx lib/pp.cmx kernel/names.cmx kernel/mod_subst.cmx \
    clib/int.cmx lib/feedback.cmx kernel/evar.cmx kernel/esubst.cmx \
    kernel/environ.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx kernel/cinstr.cmi kernel/cemitcodes.cmx \
    kernel/cbytecodes.cmx kernel/clambda.cmi
kernel/clambda.cmi : lib/pp.cmi kernel/names.cmi kernel/environ.cmi \
    kernel/constr.cmi kernel/cinstr.cmi kernel/cbytecodes.cmi
kernel/constr.cmo : lib/util.cmi kernel/univ.cmi kernel/uGraph.cmi \
    kernel/sorts.cmi kernel/names.cmi clib/int.cmi clib/hashset.cmi \
    clib/hashcons.cmi kernel/evar.cmi kernel/context.cmi clib/cArray.cmi \
    kernel/constr.cmi
kernel/constr.cmx : lib/util.cmx kernel/univ.cmx kernel/uGraph.cmx \
    kernel/sorts.cmx kernel/names.cmx clib/int.cmx clib/hashset.cmx \
    clib/hashcons.cmx kernel/evar.cmx kernel/context.cmx clib/cArray.cmx \
    kernel/constr.cmi
kernel/constr.cmi : kernel/univ.cmi kernel/uGraph.cmi kernel/sorts.cmi \
    kernel/names.cmi kernel/evar.cmi kernel/context.cmi
kernel/context.cmo : lib/util.cmi kernel/names.cmi kernel/context.cmi
kernel/context.cmx : lib/util.cmx kernel/names.cmx kernel/context.cmi
kernel/context.cmi : kernel/names.cmi
kernel/conv_oracle.cmo : lib/pp.cmi kernel/names.cmi clib/int.cmi \
    lib/cErrors.cmi kernel/conv_oracle.cmi
kernel/conv_oracle.cmx : lib/pp.cmx kernel/names.cmx clib/int.cmx \
    lib/cErrors.cmx kernel/conv_oracle.cmi
kernel/conv_oracle.cmi : kernel/names.cmi
kernel/cooking.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/term.cmi lib/pp.cmi kernel/opaqueproof.cmi kernel/names.cmi \
    kernel/mod_subst.cmi clib/hashset.cmi kernel/declarations.cmo \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi kernel/cooking.cmi
kernel/cooking.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/term.cmx lib/pp.cmx kernel/opaqueproof.cmx kernel/names.cmx \
    kernel/mod_subst.cmx clib/hashset.cmx kernel/declarations.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx kernel/cooking.cmi
kernel/cooking.cmi : kernel/opaqueproof.cmi kernel/declarations.cmo \
    kernel/constr.cmi
kernel/copcodes.cmo :
kernel/copcodes.cmx :
kernel/csymtable.cmo : kernel/vmvalues.cmi lib/util.cmi kernel/names.cmi \
    kernel/environ.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/cemitcodes.cmi kernel/cbytegen.cmi kernel/cbytecodes.cmi \
    clib/cEphemeron.cmi kernel/csymtable.cmi
kernel/csymtable.cmx : kernel/vmvalues.cmx lib/util.cmx kernel/names.cmx \
    kernel/environ.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/cemitcodes.cmx kernel/cbytegen.cmx kernel/cbytecodes.cmx \
    clib/cEphemeron.cmx kernel/csymtable.cmi
kernel/csymtable.cmi : kernel/vmvalues.cmi kernel/names.cmi \
    kernel/environ.cmi kernel/constr.cmi
kernel/declarations.cmo : kernel/vmvalues.cmi kernel/univ.cmi \
    kernel/sorts.cmi lib/rtree.cmi kernel/retroknowledge.cmi \
    kernel/opaqueproof.cmi kernel/names.cmi kernel/mod_subst.cmi \
    kernel/conv_oracle.cmi kernel/constr.cmi kernel/cemitcodes.cmi
kernel/declarations.cmx : kernel/vmvalues.cmx kernel/univ.cmx \
    kernel/sorts.cmx lib/rtree.cmx kernel/retroknowledge.cmx \
    kernel/opaqueproof.cmx kernel/names.cmx kernel/mod_subst.cmx \
    kernel/conv_oracle.cmx kernel/constr.cmx kernel/cemitcodes.cmx
kernel/declareops.cmo : lib/util.cmi kernel/univ.cmi kernel/sorts.cmi \
    lib/rtree.cmi clib/option.cmi kernel/opaqueproof.cmi kernel/names.cmi \
    kernel/mod_subst.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi kernel/cemitcodes.cmi kernel/declareops.cmi
kernel/declareops.cmx : lib/util.cmx kernel/univ.cmx kernel/sorts.cmx \
    lib/rtree.cmx clib/option.cmx kernel/opaqueproof.cmx kernel/names.cmx \
    kernel/mod_subst.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx kernel/cemitcodes.cmx kernel/declareops.cmi
kernel/declareops.cmi : kernel/univ.cmi kernel/names.cmi \
    kernel/mod_subst.cmi kernel/declarations.cmo kernel/conv_oracle.cmi
kernel/entries.cmo : kernel/univ.cmi lib/stateid.cmi kernel/names.cmi \
    lib/future.cmi kernel/declarations.cmo kernel/constr.cmi
kernel/entries.cmx : kernel/univ.cmx lib/stateid.cmx kernel/names.cmx \
    lib/future.cmx kernel/declarations.cmx kernel/constr.cmx
kernel/environ.cmo : kernel/vmvalues.cmi kernel/vars.cmi lib/util.cmi \
    kernel/univ.cmi kernel/uGraph.cmi kernel/sorts.cmi \
    kernel/retroknowledge.cmi clib/range.cmi lib/pp.cmi \
    kernel/opaqueproof.cmi kernel/names.cmi kernel/mod_subst.cmi clib/int.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/conv_oracle.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi clib/cEphemeron.cmi \
    kernel/environ.cmi
kernel/environ.cmx : kernel/vmvalues.cmx kernel/vars.cmx lib/util.cmx \
    kernel/univ.cmx kernel/uGraph.cmx kernel/sorts.cmx \
    kernel/retroknowledge.cmx clib/range.cmx lib/pp.cmx \
    kernel/opaqueproof.cmx kernel/names.cmx kernel/mod_subst.cmx clib/int.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/conv_oracle.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx clib/cEphemeron.cmx \
    kernel/environ.cmi
kernel/environ.cmi : kernel/vmvalues.cmi kernel/univ.cmi kernel/uGraph.cmi \
    kernel/sorts.cmi kernel/retroknowledge.cmi clib/range.cmi \
    kernel/opaqueproof.cmi kernel/names.cmi kernel/declarations.cmo \
    kernel/conv_oracle.cmi kernel/constr.cmi clib/cEphemeron.cmi
kernel/esubst.cmo : lib/util.cmi clib/int.cmi clib/cArray.cmi \
    kernel/esubst.cmi
kernel/esubst.cmx : lib/util.cmx clib/int.cmx clib/cArray.cmx \
    kernel/esubst.cmi
kernel/esubst.cmi : lib/util.cmi
kernel/evar.cmo : lib/pp.cmi clib/int.cmi kernel/evar.cmi
kernel/evar.cmx : lib/pp.cmx clib/int.cmx kernel/evar.cmi
kernel/evar.cmi : lib/pp.cmi clib/cMap.cmi
kernel/indtypes.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/uGraph.cmi kernel/typeops.cmi kernel/term.cmi kernel/sorts.cmi \
    lib/rtree.cmi kernel/reduction.cmi lib/pp.cmi kernel/names.cmi \
    clib/int.cmi kernel/inductive.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declareops.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi kernel/indtypes.cmi
kernel/indtypes.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/uGraph.cmx kernel/typeops.cmx kernel/term.cmx kernel/sorts.cmx \
    lib/rtree.cmx kernel/reduction.cmx lib/pp.cmx kernel/names.cmx \
    clib/int.cmx kernel/inductive.cmx kernel/environ.cmx kernel/entries.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx kernel/indtypes.cmi
kernel/indtypes.cmi : kernel/names.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo kernel/constr.cmi
kernel/inductive.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/type_errors.cmi kernel/term.cmi kernel/sorts.cmi lib/rtree.cmi \
    kernel/reduction.cmi lib/pp.cmi kernel/names.cmi clib/int.cmi \
    kernel/environ.cmi kernel/declareops.cmi kernel/declarations.cmo \
    kernel/context.cmi kernel/constr.cmi clib/cList.cmi lib/cErrors.cmi \
    kernel/inductive.cmi
kernel/inductive.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/type_errors.cmx kernel/term.cmx kernel/sorts.cmx lib/rtree.cmx \
    kernel/reduction.cmx lib/pp.cmx kernel/names.cmx clib/int.cmx \
    kernel/environ.cmx kernel/declareops.cmx kernel/declarations.cmx \
    kernel/context.cmx kernel/constr.cmx clib/cList.cmx lib/cErrors.cmx \
    kernel/inductive.cmi
kernel/inductive.cmi : kernel/univ.cmi kernel/sorts.cmi kernel/names.cmi \
    clib/int.cmi kernel/environ.cmi kernel/declarations.cmo kernel/constr.cmi
kernel/mod_subst.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    lib/pp.cmi kernel/names.cmi clib/int.cmi kernel/constr.cmi \
    kernel/mod_subst.cmi
kernel/mod_subst.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    lib/pp.cmx kernel/names.cmx clib/int.cmx kernel/constr.cmx \
    kernel/mod_subst.cmi
kernel/mod_subst.cmi : kernel/univ.cmi lib/pp.cmi kernel/names.cmi \
    kernel/constr.cmi
kernel/mod_typing.cmo : lib/util.cmi kernel/univ.cmi kernel/uGraph.cmi \
    kernel/typeops.cmi kernel/subtyping.cmi kernel/reduction.cmi \
    clib/option.cmi kernel/names.cmi kernel/modops.cmi kernel/mod_subst.cmi \
    kernel/environ.cmi kernel/entries.cmo kernel/declarations.cmo \
    kernel/cemitcodes.cmi kernel/cbytegen.cmi kernel/mod_typing.cmi
kernel/mod_typing.cmx : lib/util.cmx kernel/univ.cmx kernel/uGraph.cmx \
    kernel/typeops.cmx kernel/subtyping.cmx kernel/reduction.cmx \
    clib/option.cmx kernel/names.cmx kernel/modops.cmx kernel/mod_subst.cmx \
    kernel/environ.cmx kernel/entries.cmx kernel/declarations.cmx \
    kernel/cemitcodes.cmx kernel/cbytegen.cmx kernel/mod_typing.cmi
kernel/mod_typing.cmi : kernel/univ.cmi kernel/names.cmi \
    kernel/mod_subst.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo
kernel/modops.cmo : lib/util.cmi kernel/univ.cmi kernel/retroknowledge.cmi \
    lib/pp.cmi clib/option.cmi kernel/opaqueproof.cmi kernel/names.cmi \
    kernel/mod_subst.cmi lib/future.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declareops.cmi kernel/declarations.cmo kernel/constr.cmi \
    kernel/cemitcodes.cmi kernel/cbytegen.cmi lib/cErrors.cmi \
    kernel/modops.cmi
kernel/modops.cmx : lib/util.cmx kernel/univ.cmx kernel/retroknowledge.cmx \
    lib/pp.cmx clib/option.cmx kernel/opaqueproof.cmx kernel/names.cmx \
    kernel/mod_subst.cmx lib/future.cmx kernel/environ.cmx kernel/entries.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/constr.cmx \
    kernel/cemitcodes.cmx kernel/cbytegen.cmx lib/cErrors.cmx \
    kernel/modops.cmi
kernel/modops.cmi : kernel/univ.cmi kernel/opaqueproof.cmi kernel/names.cmi \
    kernel/mod_subst.cmi lib/future.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo kernel/constr.cmi
kernel/names.cmo : lib/util.cmi clib/unicode.cmi clib/predicate.cmi \
    lib/pp.cmi clib/option.cmi clib/int.cmi clib/hashset.cmi \
    clib/hashcons.cmi clib/hMap.cmi clib/cMap.cmi lib/cErrors.cmi \
    lib/cAst.cmi kernel/names.cmi
kernel/names.cmx : lib/util.cmx clib/unicode.cmx clib/predicate.cmx \
    lib/pp.cmx clib/option.cmx clib/int.cmx clib/hashset.cmx \
    clib/hashcons.cmx clib/hMap.cmx clib/cMap.cmx lib/cErrors.cmx \
    lib/cAst.cmx kernel/names.cmi
kernel/names.cmi : lib/util.cmi clib/predicate.cmi lib/pp.cmi clib/int.cmi \
    clib/cSig.cmi lib/cAst.cmi
kernel/nativecode.cmo : lib/util.cmi kernel/univ.cmi clib/unicode.cmi \
    kernel/uint31.cmi kernel/sorts.cmi lib/pp.cmi clib/option.cmi \
    kernel/nativevalues.cmi kernel/nativelambda.cmi kernel/nativeinstr.cmi \
    kernel/names.cmi kernel/mod_subst.cmi clib/int.cmi clib/hashset.cmi \
    lib/flags.cmi lib/feedback.cmi kernel/evar.cmi kernel/environ.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi kernel/cPrimitives.cmi lib/cErrors.cmi \
    kernel/nativecode.cmi
kernel/nativecode.cmx : lib/util.cmx kernel/univ.cmx clib/unicode.cmx \
    kernel/uint31.cmx kernel/sorts.cmx lib/pp.cmx clib/option.cmx \
    kernel/nativevalues.cmx kernel/nativelambda.cmx kernel/nativeinstr.cmi \
    kernel/names.cmx kernel/mod_subst.cmx clib/int.cmx clib/hashset.cmx \
    lib/flags.cmx lib/feedback.cmx kernel/evar.cmx kernel/environ.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx kernel/cPrimitives.cmx lib/cErrors.cmx \
    kernel/nativecode.cmi
kernel/nativecode.cmi : kernel/univ.cmi kernel/sorts.cmi \
    kernel/nativevalues.cmi kernel/nativelambda.cmi kernel/names.cmi \
    kernel/evar.cmi kernel/environ.cmi kernel/declarations.cmo \
    kernel/constr.cmi
kernel/nativeconv.cmo : kernel/vconv.cmi lib/util.cmi kernel/term.cmi \
    kernel/reduction.cmi lib/pp.cmi kernel/nativevalues.cmi \
    kernel/nativelib.cmi kernel/nativecode.cmi kernel/names.cmi clib/int.cmi \
    lib/flags.cmi lib/feedback.cmi kernel/evar.cmi kernel/environ.cmi \
    config/coq_config.cmi kernel/constr.cmi lib/cWarnings.cmi lib/cErrors.cmi \
    kernel/nativeconv.cmi
kernel/nativeconv.cmx : kernel/vconv.cmx lib/util.cmx kernel/term.cmx \
    kernel/reduction.cmx lib/pp.cmx kernel/nativevalues.cmx \
    kernel/nativelib.cmx kernel/nativecode.cmx kernel/names.cmx clib/int.cmx \
    lib/flags.cmx lib/feedback.cmx kernel/evar.cmx kernel/environ.cmx \
    config/coq_config.cmx kernel/constr.cmx lib/cWarnings.cmx lib/cErrors.cmx \
    kernel/nativeconv.cmi
kernel/nativeconv.cmi : kernel/reduction.cmi kernel/nativelambda.cmi \
    kernel/constr.cmi
kernel/nativeinstr.cmi : kernel/uint31.cmi kernel/sorts.cmi \
    kernel/nativevalues.cmi kernel/names.cmi kernel/evar.cmi \
    kernel/constr.cmi kernel/cPrimitives.cmi
kernel/nativelambda.cmo : lib/util.cmi kernel/univ.cmi kernel/uint31.cmi \
    kernel/term.cmi kernel/retroknowledge.cmi kernel/reduction.cmi \
    kernel/nativevalues.cmi kernel/nativeinstr.cmi kernel/names.cmi \
    kernel/mod_subst.cmi clib/int.cmi kernel/esubst.cmi kernel/environ.cmi \
    kernel/declarations.cmo kernel/context.cmi kernel/constr.cmi \
    kernel/cemitcodes.cmi kernel/nativelambda.cmi
kernel/nativelambda.cmx : lib/util.cmx kernel/univ.cmx kernel/uint31.cmx \
    kernel/term.cmx kernel/retroknowledge.cmx kernel/reduction.cmx \
    kernel/nativevalues.cmx kernel/nativeinstr.cmi kernel/names.cmx \
    kernel/mod_subst.cmx clib/int.cmx kernel/esubst.cmx kernel/environ.cmx \
    kernel/declarations.cmx kernel/context.cmx kernel/constr.cmx \
    kernel/cemitcodes.cmx kernel/nativelambda.cmi
kernel/nativelambda.cmi : kernel/nativeinstr.cmi kernel/names.cmi \
    kernel/environ.cmi kernel/constr.cmi kernel/cPrimitives.cmi
kernel/nativelib.cmo : lib/util.cmi lib/pp.cmi kernel/nativevalues.cmi \
    kernel/nativecode.cmi lib/flags.cmi lib/feedback.cmi lib/envars.cmi \
    config/coq_config.cmi lib/cWarnings.cmi clib/cUnix.cmi lib/cErrors.cmi \
    kernel/nativelib.cmi
kernel/nativelib.cmx : lib/util.cmx lib/pp.cmx kernel/nativevalues.cmx \
    kernel/nativecode.cmx lib/flags.cmx lib/feedback.cmx lib/envars.cmx \
    config/coq_config.cmx lib/cWarnings.cmx clib/cUnix.cmx lib/cErrors.cmx \
    kernel/nativelib.cmi
kernel/nativelib.cmi : kernel/nativevalues.cmi kernel/nativecode.cmi \
    kernel/names.cmi
kernel/nativelibrary.cmo : lib/pp.cmi kernel/nativecode.cmi kernel/names.cmi \
    kernel/modops.cmi kernel/mod_subst.cmi lib/flags.cmi lib/feedback.cmi \
    kernel/declarations.cmo kernel/nativelibrary.cmi
kernel/nativelibrary.cmx : lib/pp.cmx kernel/nativecode.cmx kernel/names.cmx \
    kernel/modops.cmx kernel/mod_subst.cmx lib/flags.cmx lib/feedback.cmx \
    kernel/declarations.cmx kernel/nativelibrary.cmi
kernel/nativelibrary.cmi : kernel/nativecode.cmi kernel/names.cmi \
    kernel/environ.cmi kernel/declarations.cmo
kernel/nativevalues.cmo : lib/util.cmi kernel/univ.cmi kernel/uint31.cmi \
    kernel/sorts.cmi lib/pp.cmi kernel/names.cmi clib/int.cmi \
    clib/hashset.cmi kernel/evar.cmi kernel/constr.cmi lib/cErrors.cmi \
    kernel/nativevalues.cmi
kernel/nativevalues.cmx : lib/util.cmx kernel/univ.cmx kernel/uint31.cmx \
    kernel/sorts.cmx lib/pp.cmx kernel/names.cmx clib/int.cmx \
    clib/hashset.cmx kernel/evar.cmx kernel/constr.cmx lib/cErrors.cmx \
    kernel/nativevalues.cmi
kernel/nativevalues.cmi : kernel/univ.cmi kernel/uint31.cmi kernel/sorts.cmi \
    kernel/names.cmi kernel/evar.cmi kernel/constr.cmi
kernel/opaqueproof.cmo : kernel/univ.cmi lib/pp.cmi kernel/names.cmi \
    kernel/mod_subst.cmi clib/int.cmi lib/future.cmi kernel/constr.cmi \
    lib/cErrors.cmi kernel/opaqueproof.cmi
kernel/opaqueproof.cmx : kernel/univ.cmx lib/pp.cmx kernel/names.cmx \
    kernel/mod_subst.cmx clib/int.cmx lib/future.cmx kernel/constr.cmx \
    lib/cErrors.cmx kernel/opaqueproof.cmi
kernel/opaqueproof.cmi : kernel/univ.cmi kernel/names.cmi \
    kernel/mod_subst.cmi lib/future.cmi kernel/constr.cmi
kernel/reduction.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/uGraph.cmi kernel/term.cmi kernel/sorts.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi lib/flags.cmi kernel/evar.cmi \
    kernel/esubst.cmi kernel/environ.cmi kernel/declarations.cmo \
    kernel/conv_oracle.cmi lib/control.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cProfile.cmi lib/cErrors.cmi kernel/cClosure.cmi \
    kernel/reduction.cmi
kernel/reduction.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/uGraph.cmx kernel/term.cmx kernel/sorts.cmx lib/pp.cmx \
    kernel/names.cmx clib/int.cmx lib/flags.cmx kernel/evar.cmx \
    kernel/esubst.cmx kernel/environ.cmx kernel/declarations.cmx \
    kernel/conv_oracle.cmx lib/control.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cProfile.cmx lib/cErrors.cmx kernel/cClosure.cmx \
    kernel/reduction.cmi
kernel/reduction.cmi : kernel/univ.cmi kernel/uGraph.cmi kernel/term.cmi \
    kernel/sorts.cmi kernel/names.cmi kernel/environ.cmi \
    kernel/declarations.cmo kernel/constr.cmi
kernel/retroknowledge.cmo : kernel/nativeinstr.cmi kernel/names.cmi \
    lib/hook.cmi kernel/constr.cmi kernel/cinstr.cmi \
    kernel/retroknowledge.cmi
kernel/retroknowledge.cmx : kernel/nativeinstr.cmi kernel/names.cmx \
    lib/hook.cmx kernel/constr.cmx kernel/cinstr.cmi \
    kernel/retroknowledge.cmi
kernel/retroknowledge.cmi : kernel/nativeinstr.cmi kernel/names.cmi \
    lib/hook.cmi kernel/constr.cmi kernel/cinstr.cmi
kernel/safe_typing.cmo : lib/util.cmi kernel/univ.cmi kernel/typeops.cmi \
    kernel/term_typing.cmi kernel/subtyping.cmi kernel/retroknowledge.cmi \
    lib/pp.cmi clib/option.cmi kernel/opaqueproof.cmi \
    kernel/nativelibrary.cmi kernel/nativelambda.cmi kernel/nativecode.cmi \
    kernel/names.cmi kernel/modops.cmi kernel/mod_typing.cmi \
    kernel/mod_subst.cmi clib/int.cmi lib/hook.cmi lib/future.cmi \
    lib/flags.cmi kernel/environ.cmi kernel/entries.cmo kernel/declareops.cmi \
    kernel/declarations.cmo kernel/cooking.cmi kernel/conv_oracle.cmi \
    kernel/context.cmi kernel/constr.cmi kernel/clambda.cmi \
    kernel/cbytecodes.cmi kernel/cPrimitives.cmi lib/cErrors.cmi \
    kernel/safe_typing.cmi
kernel/safe_typing.cmx : lib/util.cmx kernel/univ.cmx kernel/typeops.cmx \
    kernel/term_typing.cmx kernel/subtyping.cmx kernel/retroknowledge.cmx \
    lib/pp.cmx clib/option.cmx kernel/opaqueproof.cmx \
    kernel/nativelibrary.cmx kernel/nativelambda.cmx kernel/nativecode.cmx \
    kernel/names.cmx kernel/modops.cmx kernel/mod_typing.cmx \
    kernel/mod_subst.cmx clib/int.cmx lib/hook.cmx lib/future.cmx \
    lib/flags.cmx kernel/environ.cmx kernel/entries.cmx kernel/declareops.cmx \
    kernel/declarations.cmx kernel/cooking.cmx kernel/conv_oracle.cmx \
    kernel/context.cmx kernel/constr.cmx kernel/clambda.cmx \
    kernel/cbytecodes.cmx kernel/cPrimitives.cmx lib/cErrors.cmx \
    kernel/safe_typing.cmi
kernel/safe_typing.cmi : kernel/univ.cmi kernel/retroknowledge.cmi \
    kernel/nativecode.cmi kernel/names.cmi kernel/mod_subst.cmi \
    lib/future.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo kernel/cooking.cmi kernel/conv_oracle.cmi \
    kernel/constr.cmi
kernel/sorts.cmo : kernel/univ.cmi clib/int.cmi clib/hashset.cmi \
    clib/hashcons.cmi clib/cList.cmi kernel/sorts.cmi
kernel/sorts.cmx : kernel/univ.cmx clib/int.cmx clib/hashset.cmx \
    clib/hashcons.cmx clib/cList.cmx kernel/sorts.cmi
kernel/sorts.cmi : kernel/univ.cmi
kernel/subtyping.cmo : lib/util.cmi kernel/univ.cmi kernel/uGraph.cmi \
    kernel/reduction.cmi lib/pp.cmi kernel/names.cmi kernel/modops.cmi \
    kernel/mod_subst.cmi clib/int.cmi kernel/inductive.cmi kernel/environ.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/constr.cmi \
    clib/cList.cmi lib/cErrors.cmi kernel/subtyping.cmi
kernel/subtyping.cmx : lib/util.cmx kernel/univ.cmx kernel/uGraph.cmx \
    kernel/reduction.cmx lib/pp.cmx kernel/names.cmx kernel/modops.cmx \
    kernel/mod_subst.cmx clib/int.cmx kernel/inductive.cmx kernel/environ.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/constr.cmx \
    clib/cList.cmx lib/cErrors.cmx kernel/subtyping.cmi
kernel/subtyping.cmi : kernel/univ.cmi kernel/environ.cmi \
    kernel/declarations.cmo
kernel/term.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/sorts.cmi lib/pp.cmi kernel/names.cmi clib/int.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi kernel/term.cmi
kernel/term.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/sorts.cmx lib/pp.cmx kernel/names.cmx clib/int.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx kernel/term.cmi
kernel/term.cmi : kernel/univ.cmi kernel/sorts.cmi kernel/names.cmi \
    kernel/constr.cmi
kernel/term_typing.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/typeops.cmi lib/pp.cmi clib/option.cmi kernel/opaqueproof.cmi \
    kernel/names.cmi kernel/mod_subst.cmi clib/int.cmi kernel/indtypes.cmi \
    lib/future.cmi lib/flags.cmi lib/feedback.cmi kernel/environ.cmi \
    kernel/entries.cmo kernel/declareops.cmi kernel/declarations.cmo \
    kernel/cooking.cmi kernel/context.cmi kernel/constr.cmi \
    kernel/cemitcodes.cmi kernel/cbytegen.cmi clib/cList.cmi lib/cErrors.cmi \
    clib/cEphemeron.cmi lib/aux_file.cmi kernel/term_typing.cmi
kernel/term_typing.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/typeops.cmx lib/pp.cmx clib/option.cmx kernel/opaqueproof.cmx \
    kernel/names.cmx kernel/mod_subst.cmx clib/int.cmx kernel/indtypes.cmx \
    lib/future.cmx lib/flags.cmx lib/feedback.cmx kernel/environ.cmx \
    kernel/entries.cmx kernel/declareops.cmx kernel/declarations.cmx \
    kernel/cooking.cmx kernel/context.cmx kernel/constr.cmx \
    kernel/cemitcodes.cmx kernel/cbytegen.cmx clib/cList.cmx lib/cErrors.cmx \
    clib/cEphemeron.cmx lib/aux_file.cmx kernel/term_typing.cmi
kernel/term_typing.cmi : kernel/names.cmi kernel/environ.cmi \
    kernel/entries.cmo kernel/declarations.cmo kernel/cooking.cmi \
    kernel/constr.cmi
kernel/type_errors.cmo : kernel/univ.cmi kernel/sorts.cmi \
    kernel/reduction.cmi kernel/names.cmi kernel/environ.cmi \
    kernel/constr.cmi kernel/type_errors.cmi
kernel/type_errors.cmx : kernel/univ.cmx kernel/sorts.cmx \
    kernel/reduction.cmx kernel/names.cmx kernel/environ.cmx \
    kernel/constr.cmx kernel/type_errors.cmi
kernel/type_errors.cmi : kernel/univ.cmi kernel/sorts.cmi kernel/names.cmi \
    kernel/environ.cmi kernel/constr.cmi
kernel/typeops.cmo : kernel/vconv.cmi kernel/vars.cmi lib/util.cmi \
    kernel/univ.cmi kernel/uGraph.cmi kernel/type_errors.cmi kernel/sorts.cmi \
    kernel/reduction.cmi lib/pp.cmi clib/option.cmi kernel/nativelambda.cmi \
    kernel/nativeconv.cmi kernel/names.cmi clib/int.cmi kernel/inductive.cmi \
    lib/flags.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo kernel/context.cmi kernel/constr.cmi \
    lib/cProfile.cmi clib/cList.cmi lib/cErrors.cmi kernel/typeops.cmi
kernel/typeops.cmx : kernel/vconv.cmx kernel/vars.cmx lib/util.cmx \
    kernel/univ.cmx kernel/uGraph.cmx kernel/type_errors.cmx kernel/sorts.cmx \
    kernel/reduction.cmx lib/pp.cmx clib/option.cmx kernel/nativelambda.cmx \
    kernel/nativeconv.cmx kernel/names.cmx clib/int.cmx kernel/inductive.cmx \
    lib/flags.cmx kernel/environ.cmx kernel/entries.cmx \
    kernel/declarations.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cProfile.cmx clib/cList.cmx lib/cErrors.cmx kernel/typeops.cmi
kernel/typeops.cmi : kernel/univ.cmi kernel/sorts.cmi kernel/names.cmi \
    kernel/environ.cmi kernel/entries.cmo kernel/constr.cmi
kernel/uGraph.cmo : lib/util.cmi kernel/univ.cmi clib/unionfind.cmi \
    lib/pp.cmi kernel/names.cmi clib/int.cmi lib/flags.cmi lib/cProfile.cmi \
    lib/cErrors.cmi kernel/uGraph.cmi
kernel/uGraph.cmx : lib/util.cmx kernel/univ.cmx clib/unionfind.cmx \
    lib/pp.cmx kernel/names.cmx clib/int.cmx lib/flags.cmx lib/cProfile.cmx \
    lib/cErrors.cmx kernel/uGraph.cmi
kernel/uGraph.cmi : kernel/univ.cmi lib/pp.cmi
kernel/uint31.cmo : kernel/uint31.cmi
kernel/uint31.cmx : kernel/uint31.cmi
kernel/uint31.cmi :
kernel/univ.cmo : lib/util.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    clib/int.cmi clib/hashset.cmi clib/hashcons.cmi clib/hMap.cmi \
    clib/cList.cmi lib/cErrors.cmi clib/cArray.cmi kernel/univ.cmi
kernel/univ.cmx : lib/util.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    clib/int.cmx clib/hashset.cmx clib/hashcons.cmx clib/hMap.cmx \
    clib/cList.cmx lib/cErrors.cmx clib/cArray.cmx kernel/univ.cmi
kernel/univ.cmi : lib/pp.cmi kernel/names.cmi clib/cSig.cmi clib/cMap.cmi
kernel/vars.cmo : kernel/univ.cmi kernel/sorts.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi kernel/esubst.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi kernel/vars.cmi
kernel/vars.cmx : kernel/univ.cmx kernel/sorts.cmx lib/pp.cmx \
    kernel/names.cmx clib/int.cmx kernel/esubst.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx kernel/vars.cmi
kernel/vars.cmi : kernel/univ.cmi kernel/names.cmi kernel/esubst.cmi \
    kernel/context.cmi kernel/constr.cmi
kernel/vconv.cmo : kernel/vmvalues.cmi kernel/vm.cmi lib/util.cmi \
    kernel/univ.cmi kernel/reduction.cmi lib/pp.cmi kernel/names.cmi \
    clib/int.cmi kernel/environ.cmi kernel/declarations.cmo \
    kernel/csymtable.cmi config/coq_config.cmi kernel/constr.cmi \
    lib/cWarnings.cmi kernel/vconv.cmi
kernel/vconv.cmx : kernel/vmvalues.cmx kernel/vm.cmx lib/util.cmx \
    kernel/univ.cmx kernel/reduction.cmx lib/pp.cmx kernel/names.cmx \
    clib/int.cmx kernel/environ.cmx kernel/declarations.cmx \
    kernel/csymtable.cmx config/coq_config.cmx kernel/constr.cmx \
    lib/cWarnings.cmx kernel/vconv.cmi
kernel/vconv.cmi : kernel/reduction.cmi kernel/constr.cmi
kernel/vm.cmo : kernel/vmvalues.cmi clib/int.cmi kernel/csymtable.cmi \
    kernel/vm.cmi
kernel/vm.cmx : kernel/vmvalues.cmx clib/int.cmx kernel/csymtable.cmx \
    kernel/vm.cmi
kernel/vm.cmi : kernel/vmvalues.cmi
kernel/vmvalues.cmo : kernel/univ.cmi kernel/sorts.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi clib/hashset.cmi kernel/evar.cmi \
    kernel/constr.cmi lib/cErrors.cmi clib/cArray.cmi kernel/vmvalues.cmi
kernel/vmvalues.cmx : kernel/univ.cmx kernel/sorts.cmx lib/pp.cmx \
    kernel/names.cmx clib/int.cmx clib/hashset.cmx kernel/evar.cmx \
    kernel/constr.cmx lib/cErrors.cmx clib/cArray.cmx kernel/vmvalues.cmi
kernel/vmvalues.cmi : kernel/univ.cmi kernel/sorts.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi kernel/evar.cmi kernel/constr.cmi
lib/aux_file.cmo : lib/pp.cmi clib/option.cmi lib/loc.cmi lib/flags.cmi \
    lib/feedback.cmi clib/cUnix.cmi lib/aux_file.cmi
lib/aux_file.cmx : lib/pp.cmx clib/option.cmx lib/loc.cmx lib/flags.cmx \
    lib/feedback.cmx clib/cUnix.cmx lib/aux_file.cmi
lib/aux_file.cmi : lib/loc.cmi
lib/cAst.cmo : lib/loc.cmi lib/cAst.cmi
lib/cAst.cmx : lib/loc.cmx lib/cAst.cmi
lib/cAst.cmi : lib/loc.cmi
lib/cErrors.cmo : lib/pp.cmi lib/loc.cmi lib/flags.cmi clib/exninfo.cmi \
    config/coq_config.cmi clib/backtrace.cmi lib/cErrors.cmi
lib/cErrors.cmx : lib/pp.cmx lib/loc.cmx lib/flags.cmx clib/exninfo.cmx \
    config/coq_config.cmx clib/backtrace.cmx lib/cErrors.cmi
lib/cErrors.cmi : lib/pp.cmi lib/loc.cmi clib/exninfo.cmi
lib/cProfile.cmo : lib/flags.cmi clib/cObj.cmi lib/cErrors.cmi \
    lib/cProfile.cmi
lib/cProfile.cmx : lib/flags.cmx clib/cObj.cmx lib/cErrors.cmx \
    lib/cProfile.cmi
lib/cProfile.cmi :
lib/cWarnings.cmo : lib/pp.cmi lib/flags.cmi lib/feedback.cmi \
    clib/cString.cmi clib/cList.cmi lib/cErrors.cmi lib/cWarnings.cmi
lib/cWarnings.cmx : lib/pp.cmx lib/flags.cmx lib/feedback.cmx \
    clib/cString.cmx clib/cList.cmx lib/cErrors.cmx lib/cWarnings.cmi
lib/cWarnings.cmi : lib/pp.cmi lib/loc.cmi
lib/control.cmo : clib/exninfo.cmi clib/backtrace.cmi lib/control.cmi
lib/control.cmx : clib/exninfo.cmx clib/backtrace.cmx lib/control.cmi
lib/control.cmi :
lib/coqProject_file.cmo : lib/pp.cmi clib/option.cmi lib/feedback.cmi \
    clib/cUnix.cmi clib/cList.cmi lib/coqProject_file.cmi
lib/coqProject_file.cmx : lib/pp.cmx clib/option.cmx lib/feedback.cmx \
    clib/cUnix.cmx clib/cList.cmx lib/coqProject_file.cmi
lib/coqProject_file.cmi :
lib/dAst.cmo : lib/cAst.cmi lib/dAst.cmi
lib/dAst.cmx : lib/cAst.cmx lib/dAst.cmi
lib/dAst.cmi : lib/loc.cmi lib/cAst.cmi
lib/envars.cmo : lib/util.cmi clib/int.cmi lib/flags.cmi \
    config/coq_config.cmi clib/cUnix.cmi lib/envars.cmi
lib/envars.cmx : lib/util.cmx clib/int.cmx lib/flags.cmx \
    config/coq_config.cmx clib/cUnix.cmx lib/envars.cmi
lib/envars.cmi :
lib/explore.cmo : lib/pp.cmi lib/feedback.cmi lib/explore.cmi
lib/explore.cmx : lib/pp.cmx lib/feedback.cmx lib/explore.cmi
lib/explore.cmi : lib/pp.cmi
lib/feedback.cmo : lib/xml_datatype.cmi lib/stateid.cmi lib/pp.cmi \
    clib/option.cmi lib/loc.cmi lib/feedback.cmi
lib/feedback.cmx : lib/xml_datatype.cmi lib/stateid.cmx lib/pp.cmx \
    clib/option.cmx lib/loc.cmx lib/feedback.cmi
lib/feedback.cmi : lib/xml_datatype.cmi lib/stateid.cmi lib/pp.cmi \
    lib/loc.cmi
lib/flags.cmo : clib/exninfo.cmi config/coq_config.cmi clib/backtrace.cmi \
    lib/flags.cmi
lib/flags.cmx : clib/exninfo.cmx config/coq_config.cmx clib/backtrace.cmx \
    lib/flags.cmi
lib/flags.cmi :
lib/future.cmo : lib/pp.cmi clib/exninfo.cmi clib/cList.cmi lib/cErrors.cmi \
    clib/cEphemeron.cmi lib/future.cmi
lib/future.cmx : lib/pp.cmx clib/exninfo.cmx clib/cList.cmx lib/cErrors.cmx \
    clib/cEphemeron.cmx lib/future.cmi
lib/future.cmi : lib/pp.cmi clib/exninfo.cmi
lib/genarg.cmo : lib/util.cmi lib/pp.cmi clib/dyn.cmi clib/cSig.cmi \
    lib/cErrors.cmi lib/genarg.cmi
lib/genarg.cmx : lib/util.cmx lib/pp.cmx clib/dyn.cmx clib/cSig.cmi \
    lib/cErrors.cmx lib/genarg.cmi
lib/genarg.cmi : lib/pp.cmi clib/cSig.cmi
lib/hook.cmo : lib/hook.cmi
lib/hook.cmx : lib/hook.cmi
lib/hook.cmi :
lib/loc.cmo : clib/exninfo.cmi lib/loc.cmi
lib/loc.cmx : clib/exninfo.cmx lib/loc.cmi
lib/loc.cmi : clib/exninfo.cmi
lib/pp.cmo : clib/exninfo.cmi clib/cArray.cmi clib/backtrace.cmi lib/pp.cmi
lib/pp.cmx : clib/exninfo.cmx clib/cArray.cmx clib/backtrace.cmx lib/pp.cmi
lib/pp.cmi :
lib/pp_diff.cmo : lib/pp.cmi clib/diff2.cmi lib/pp_diff.cmi
lib/pp_diff.cmx : lib/pp.cmx clib/diff2.cmx lib/pp_diff.cmi
lib/pp_diff.cmi : lib/pp.cmi clib/diff2.cmi
lib/remoteCounter.cmo : lib/pp.cmi lib/flags.cmi lib/cErrors.cmi \
    lib/remoteCounter.cmi
lib/remoteCounter.cmx : lib/pp.cmx lib/flags.cmx lib/cErrors.cmx \
    lib/remoteCounter.cmi
lib/remoteCounter.cmi :
lib/rtree.cmo : lib/util.cmi lib/pp.cmi clib/int.cmi lib/rtree.cmi
lib/rtree.cmx : lib/util.cmx lib/pp.cmx clib/int.cmx lib/rtree.cmi
lib/rtree.cmi : lib/pp.cmi
lib/spawn.cmo : clib/option.cmi lib/flags.cmi lib/cErrors.cmi lib/spawn.cmi
lib/spawn.cmx : clib/option.cmx lib/flags.cmx lib/cErrors.cmx lib/spawn.cmi
lib/spawn.cmi :
lib/stateid.cmo : lib/loc.cmi clib/int.cmi clib/exninfo.cmi lib/stateid.cmi
lib/stateid.cmx : lib/loc.cmx clib/int.cmx clib/exninfo.cmx lib/stateid.cmi
lib/stateid.cmi : lib/loc.cmi clib/exninfo.cmi
lib/system.cmo : lib/util.cmi lib/pp.cmi clib/minisys.cmo clib/int.cmi \
    lib/feedback.cmi lib/cWarnings.cmi clib/cUnix.cmi lib/cErrors.cmi \
    lib/system.cmi
lib/system.cmx : lib/util.cmx lib/pp.cmx clib/minisys.cmx clib/int.cmx \
    lib/feedback.cmx lib/cWarnings.cmx clib/cUnix.cmx lib/cErrors.cmx \
    lib/system.cmi
lib/system.cmi : lib/pp.cmi clib/cUnix.cmi
lib/util.cmo : clib/int.cmi clib/exninfo.cmi clib/cString.cmi \
    clib/cStack.cmi clib/cSig.cmi clib/cSet.cmi clib/cMap.cmi clib/cList.cmi \
    clib/cArray.cmi lib/util.cmi
lib/util.cmx : clib/int.cmx clib/exninfo.cmx clib/cString.cmx \
    clib/cStack.cmx clib/cSig.cmi clib/cSet.cmx clib/cMap.cmx clib/cList.cmx \
    clib/cArray.cmx lib/util.cmi
lib/util.cmi : clib/exninfo.cmi clib/cString.cmi clib/cStack.cmi \
    clib/cSig.cmi clib/cSet.cmi clib/cMap.cmi clib/cList.cmi clib/cArray.cmi
lib/xml_datatype.cmi :
library/coqlib.cmo : lib/util.cmi lib/pp.cmi library/nametab.cmi \
    kernel/names.cmi library/library.cmi library/libnames.cmi library/lib.cmi \
    library/globnames.cmi lib/cErrors.cmi library/coqlib.cmi
library/coqlib.cmx : lib/util.cmx lib/pp.cmx library/nametab.cmx \
    kernel/names.cmx library/library.cmx library/libnames.cmx library/lib.cmx \
    library/globnames.cmx lib/cErrors.cmx library/coqlib.cmi
library/coqlib.cmi : lib/util.cmi kernel/names.cmi library/libnames.cmi
library/decl_kinds.cmo :
library/decl_kinds.cmx :
library/declaremods.cmo : lib/util.cmi kernel/univ.cmi library/summary.cmi \
    kernel/subtyping.cmi kernel/safe_typing.cmi lib/pp.cmi \
    library/nametab.cmi kernel/names.cmi kernel/modops.cmi \
    kernel/mod_typing.cmi kernel/mod_subst.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi clib/int.cmi library/global.cmi \
    lib/flags.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo lib/cErrors.cmi lib/cAst.cmi \
    library/declaremods.cmi
library/declaremods.cmx : lib/util.cmx kernel/univ.cmx library/summary.cmx \
    kernel/subtyping.cmx kernel/safe_typing.cmx lib/pp.cmx \
    library/nametab.cmx kernel/names.cmx kernel/modops.cmx \
    kernel/mod_typing.cmx kernel/mod_subst.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx library/global.cmx \
    lib/flags.cmx kernel/environ.cmx kernel/entries.cmx \
    kernel/declarations.cmx lib/cErrors.cmx lib/cAst.cmx \
    library/declaremods.cmi
library/declaremods.cmi : kernel/univ.cmi kernel/safe_typing.cmi lib/pp.cmi \
    kernel/nativecode.cmi kernel/names.cmi library/libobject.cmi \
    library/libnames.cmi lib/future.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo
library/decls.cmo : lib/util.cmi kernel/univ.cmi library/summary.cmi \
    kernel/names.cmi library/libnames.cmi library/lib.cmi library/global.cmi \
    kernel/environ.cmi library/decl_kinds.cmo kernel/context.cmi \
    library/decls.cmi
library/decls.cmx : lib/util.cmx kernel/univ.cmx library/summary.cmx \
    kernel/names.cmx library/libnames.cmx library/lib.cmx library/global.cmx \
    kernel/environ.cmx library/decl_kinds.cmx kernel/context.cmx \
    library/decls.cmi
library/decls.cmi : kernel/univ.cmi kernel/names.cmi library/libnames.cmi \
    kernel/environ.cmi library/decl_kinds.cmo
library/dischargedhypsmap.cmo : library/summary.cmi library/libnames.cmi \
    library/dischargedhypsmap.cmi
library/dischargedhypsmap.cmx : library/summary.cmx library/libnames.cmx \
    library/dischargedhypsmap.cmi
library/dischargedhypsmap.cmi : library/libnames.cmi
library/global.cmo : kernel/univ.cmi library/summary.cmi \
    kernel/safe_typing.cmi lib/pp.cmi kernel/opaqueproof.cmi kernel/names.cmi \
    kernel/mod_subst.cmi kernel/inductive.cmi library/globnames.cmi \
    lib/future.cmi lib/flags.cmi kernel/environ.cmi kernel/declareops.cmi \
    kernel/declarations.cmo kernel/constr.cmi lib/cErrors.cmi \
    library/global.cmi
library/global.cmx : kernel/univ.cmx library/summary.cmx \
    kernel/safe_typing.cmx lib/pp.cmx kernel/opaqueproof.cmx kernel/names.cmx \
    kernel/mod_subst.cmx kernel/inductive.cmx library/globnames.cmx \
    lib/future.cmx lib/flags.cmx kernel/environ.cmx kernel/declareops.cmx \
    kernel/declarations.cmx kernel/constr.cmx lib/cErrors.cmx \
    library/global.cmi
library/global.cmi : kernel/univ.cmi kernel/uGraph.cmi library/summary.cmi \
    kernel/safe_typing.cmi kernel/retroknowledge.cmi kernel/opaqueproof.cmi \
    kernel/names.cmi kernel/mod_subst.cmi lib/future.cmi kernel/environ.cmi \
    kernel/entries.cmo kernel/declarations.cmo kernel/conv_oracle.cmi \
    kernel/constr.cmi
library/globnames.cmo : lib/pp.cmi kernel/names.cmi kernel/mod_subst.cmi \
    library/libnames.cmi clib/hashset.cmi clib/hMap.cmi kernel/constr.cmi \
    lib/cErrors.cmi library/globnames.cmi
library/globnames.cmx : lib/pp.cmx kernel/names.cmx kernel/mod_subst.cmx \
    library/libnames.cmx clib/hashset.cmx clib/hMap.cmx kernel/constr.cmx \
    lib/cErrors.cmx library/globnames.cmi
library/globnames.cmi : lib/util.cmi kernel/names.cmi kernel/mod_subst.cmi \
    kernel/constr.cmi clib/cSig.cmi
library/goptions.cmo : lib/util.cmi library/summary.cmi lib/pp.cmi \
    kernel/mod_subst.cmi library/libobject.cmi library/libnames.cmi \
    library/lib.cmi clib/int.cmi lib/feedback.cmi lib/cWarnings.cmi \
    lib/cErrors.cmi library/goptions.cmi
library/goptions.cmx : lib/util.cmx library/summary.cmx lib/pp.cmx \
    kernel/mod_subst.cmx library/libobject.cmx library/libnames.cmx \
    library/lib.cmx clib/int.cmx lib/feedback.cmx lib/cWarnings.cmx \
    lib/cErrors.cmx library/goptions.cmi
library/goptions.cmi : lib/pp.cmi kernel/mod_subst.cmi library/libnames.cmi \
    clib/cSig.cmi
library/keys.cmo : library/summary.cmi lib/pp.cmi kernel/names.cmi \
    library/libobject.cmi library/lib.cmi clib/int.cmi clib/hMap.cmi \
    library/globnames.cmi kernel/constr.cmi library/keys.cmi
library/keys.cmx : library/summary.cmx lib/pp.cmx kernel/names.cmx \
    library/libobject.cmx library/lib.cmx clib/int.cmx clib/hMap.cmx \
    library/globnames.cmx kernel/constr.cmx library/keys.cmi
library/keys.cmi : lib/pp.cmi kernel/names.cmi kernel/constr.cmi
library/kindops.cmo : lib/pp.cmi library/decl_kinds.cmo lib/cErrors.cmi \
    library/kindops.cmi
library/kindops.cmx : lib/pp.cmx library/decl_kinds.cmx lib/cErrors.cmx \
    library/kindops.cmi
library/kindops.cmi : library/decl_kinds.cmo
library/lib.cmo : lib/util.cmi kernel/univ.cmi library/summary.cmi \
    lib/pp.cmi clib/option.cmi kernel/opaqueproof.cmi library/nametab.cmi \
    kernel/names.cmi library/libobject.cmi library/libnames.cmi \
    library/globnames.cmi library/decl_kinds.cmo kernel/context.cmi \
    kernel/constr.cmi clib/cList.cmi lib/cErrors.cmi library/lib.cmi
library/lib.cmx : lib/util.cmx kernel/univ.cmx library/summary.cmx \
    lib/pp.cmx clib/option.cmx kernel/opaqueproof.cmx library/nametab.cmx \
    kernel/names.cmx library/libobject.cmx library/libnames.cmx \
    library/globnames.cmx library/decl_kinds.cmx kernel/context.cmx \
    kernel/constr.cmx clib/cList.cmx lib/cErrors.cmx library/lib.cmi
library/lib.cmi : kernel/univ.cmi library/summary.cmi kernel/opaqueproof.cmi \
    kernel/names.cmi kernel/mod_subst.cmi library/libobject.cmi \
    library/libnames.cmi library/decl_kinds.cmo kernel/constr.cmi
library/libnames.cmo : lib/util.cmi lib/pp.cmi kernel/names.cmi clib/int.cmi \
    lib/cErrors.cmi lib/cAst.cmi library/libnames.cmi
library/libnames.cmx : lib/util.cmx lib/pp.cmx kernel/names.cmx clib/int.cmx \
    lib/cErrors.cmx lib/cAst.cmx library/libnames.cmi
library/libnames.cmi : lib/util.cmi lib/pp.cmi kernel/names.cmi lib/loc.cmi \
    clib/cSig.cmi lib/cAst.cmi
library/libobject.cmo : lib/pp.cmi clib/option.cmi kernel/mod_subst.cmi \
    library/libnames.cmi clib/dyn.cmi lib/cErrors.cmi library/libobject.cmi
library/libobject.cmx : lib/pp.cmx clib/option.cmx kernel/mod_subst.cmx \
    library/libnames.cmx clib/dyn.cmx lib/cErrors.cmx library/libobject.cmi
library/libobject.cmi : kernel/mod_subst.cmi library/libnames.cmi
library/library.cmo : lib/util.cmi kernel/univ.cmi lib/system.cmi \
    library/summary.cmi lib/stateid.cmi kernel/safe_typing.cmi lib/pp.cmi \
    clib/option.cmi kernel/opaqueproof.cmi kernel/nativelib.cmi \
    kernel/nativecode.cmi library/nametab.cmi kernel/names.cmi \
    library/loadpath.cmi library/libobject.cmi library/libnames.cmi \
    library/lib.cmi clib/int.cmi lib/future.cmi lib/flags.cmi \
    lib/feedback.cmi library/declaremods.cmi config/coq_config.cmi \
    kernel/constr.cmi lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    library/library.cmi
library/library.cmx : lib/util.cmx kernel/univ.cmx lib/system.cmx \
    library/summary.cmx lib/stateid.cmx kernel/safe_typing.cmx lib/pp.cmx \
    clib/option.cmx kernel/opaqueproof.cmx kernel/nativelib.cmx \
    kernel/nativecode.cmx library/nametab.cmx kernel/names.cmx \
    library/loadpath.cmx library/libobject.cmx library/libnames.cmx \
    library/lib.cmx clib/int.cmx lib/future.cmx lib/flags.cmx \
    lib/feedback.cmx library/declaremods.cmx config/coq_config.cmx \
    kernel/constr.cmx lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    library/library.cmi
library/library.cmi : kernel/univ.cmi lib/stateid.cmi kernel/opaqueproof.cmi \
    kernel/names.cmi library/libnames.cmi lib/future.cmi kernel/constr.cmi \
    clib/cUnix.cmi
library/loadpath.cmo : lib/util.cmi lib/system.cmi library/summary.cmi \
    lib/pp.cmi kernel/names.cmi library/libnames.cmi lib/flags.cmi \
    lib/cWarnings.cmi clib/cUnix.cmi lib/cErrors.cmi library/loadpath.cmi
library/loadpath.cmx : lib/util.cmx lib/system.cmx library/summary.cmx \
    lib/pp.cmx kernel/names.cmx library/libnames.cmx lib/flags.cmx \
    lib/cWarnings.cmx clib/cUnix.cmx lib/cErrors.cmx library/loadpath.cmi
library/loadpath.cmi : kernel/names.cmi clib/cUnix.cmi
library/nametab.cmo : lib/util.cmi library/summary.cmi lib/pp.cmi \
    kernel/names.cmi lib/loc.cmi library/libnames.cmi clib/int.cmi \
    clib/hMap.cmi library/globnames.cmi lib/flags.cmi lib/feedback.cmi \
    lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi library/nametab.cmi
library/nametab.cmx : lib/util.cmx library/summary.cmx lib/pp.cmx \
    kernel/names.cmx lib/loc.cmx library/libnames.cmx clib/int.cmx \
    clib/hMap.cmx library/globnames.cmx lib/flags.cmx lib/feedback.cmx \
    lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx library/nametab.cmi
library/nametab.cmi : lib/pp.cmi kernel/names.cmi lib/loc.cmi \
    library/libnames.cmi library/globnames.cmi clib/cMap.cmi
library/states.cmo : lib/util.cmi lib/system.cmi library/summary.cmi \
    library/library.cmi library/lib.cmi config/coq_config.cmi lib/cErrors.cmi \
    library/states.cmi
library/states.cmx : lib/util.cmx lib/system.cmx library/summary.cmx \
    library/library.cmx library/lib.cmx config/coq_config.cmx lib/cErrors.cmx \
    library/states.cmi
library/states.cmi : library/summary.cmi
library/summary.cmo : lib/util.cmi lib/pp.cmi clib/option.cmi clib/dyn.cmi \
    lib/cWarnings.cmi lib/cErrors.cmi clib/cEphemeron.cmi library/summary.cmi
library/summary.cmx : lib/util.cmx lib/pp.cmx clib/option.cmx clib/dyn.cmx \
    lib/cWarnings.cmx lib/cErrors.cmx clib/cEphemeron.cmx library/summary.cmi
library/summary.cmi : clib/dyn.cmi
parsing/cLexer.cmo : lib/util.cmi clib/unicode.cmi parsing/tok.cmi \
    lib/pp.cmi clib/option.cmi lib/loc.cmi clib/int.cmi lib/flags.cmi \
    lib/feedback.cmi lib/cWarnings.cmi clib/cString.cmi parsing/cLexer.cmi
parsing/cLexer.cmx : lib/util.cmx clib/unicode.cmx parsing/tok.cmx \
    lib/pp.cmx clib/option.cmx lib/loc.cmx clib/int.cmx lib/flags.cmx \
    lib/feedback.cmx lib/cWarnings.cmx clib/cString.cmx parsing/cLexer.cmi
parsing/cLexer.cmi : parsing/tok.cmi lib/loc.cmi clib/cString.cmi
parsing/extend.cmo : parsing/tok.cmi interp/notation_term.cmo lib/loc.cmi \
    lib/genarg.cmi interp/constrexpr.cmo parsing/cLexer.cmi
parsing/extend.cmx : parsing/tok.cmx interp/notation_term.cmx lib/loc.cmx \
    lib/genarg.cmx interp/constrexpr.cmx parsing/cLexer.cmx
parsing/g_constr.cmo : lib/util.cmi parsing/tok.cmi kernel/sorts.cmi \
    lib/pp.cmi parsing/pcoq.cmi clib/option.cmi kernel/names.cmi \
    engine/namegen.cmi lib/loc.cmi library/libnames.cmi \
    pretyping/glob_term.cmo parsing/extend.cmo engine/evar_kinds.cmi \
    library/decl_kinds.cmo interp/constrexpr_ops.cmi interp/constrexpr.cmo \
    kernel/constr.cmi parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi
parsing/g_constr.cmx : lib/util.cmx parsing/tok.cmx kernel/sorts.cmx \
    lib/pp.cmx parsing/pcoq.cmx clib/option.cmx kernel/names.cmx \
    engine/namegen.cmx lib/loc.cmx library/libnames.cmx \
    pretyping/glob_term.cmx parsing/extend.cmx engine/evar_kinds.cmx \
    library/decl_kinds.cmx interp/constrexpr_ops.cmx interp/constrexpr.cmx \
    kernel/constr.cmx parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx
parsing/g_prim.cmo : parsing/tok.cmi lib/pp.cmi parsing/pcoq.cmi \
    kernel/names.cmi library/libnames.cmi parsing/extend.cmo \
    interp/constrexpr.cmo parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi
parsing/g_prim.cmx : parsing/tok.cmx lib/pp.cmx parsing/pcoq.cmx \
    kernel/names.cmx library/libnames.cmx parsing/extend.cmx \
    interp/constrexpr.cmx parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx
parsing/notation_gram.cmo : parsing/tok.cmi kernel/names.cmi \
    parsing/extend.cmo interp/constrexpr.cmo
parsing/notation_gram.cmx : parsing/tok.cmx kernel/names.cmx \
    parsing/extend.cmx interp/constrexpr.cmx
parsing/notgram_ops.cmo : lib/util.cmi library/summary.cmi lib/pp.cmi \
    clib/option.cmi parsing/notation_gram.cmo interp/notation.cmi \
    clib/int.cmi parsing/extend.cmo lib/cErrors.cmi parsing/notgram_ops.cmi
parsing/notgram_ops.cmx : lib/util.cmx library/summary.cmx lib/pp.cmx \
    clib/option.cmx parsing/notation_gram.cmx interp/notation.cmx \
    clib/int.cmx parsing/extend.cmx lib/cErrors.cmx parsing/notgram_ops.cmi
parsing/notgram_ops.cmi : parsing/notation_gram.cmo interp/constrexpr.cmo
parsing/pcoq.cmo : lib/util.cmi parsing/tok.cmi library/summary.cmi \
    clib/store.cmi interp/stdarg.cmi lib/pp.cmi clib/option.cmi lib/loc.cmi \
    lib/genarg.cmi parsing/extend.cmo clib/exninfo.cmi clib/dyn.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi parsing/pcoq.cmi
parsing/pcoq.cmx : lib/util.cmx parsing/tok.cmx library/summary.cmx \
    clib/store.cmx interp/stdarg.cmx lib/pp.cmx clib/option.cmx lib/loc.cmx \
    lib/genarg.cmx parsing/extend.cmx clib/exninfo.cmx clib/dyn.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx parsing/pcoq.cmi
parsing/pcoq.cmi : parsing/tok.cmi library/summary.cmi clib/store.cmi \
    kernel/sorts.cmi kernel/names.cmi lib/loc.cmi library/libnames.cmi \
    pretyping/glob_term.cmo lib/genarg.cmi parsing/extend.cmo \
    interp/constrexpr.cmo parsing/cLexer.cmi lib/cAst.cmi
parsing/ppextend.cmo : lib/util.cmi library/summary.cmi lib/pp.cmi \
    parsing/notation_gram.cmo interp/notation.cmi lib/loc.cmi lib/cErrors.cmi \
    parsing/ppextend.cmi
parsing/ppextend.cmx : lib/util.cmx library/summary.cmx lib/pp.cmx \
    parsing/notation_gram.cmx interp/notation.cmx lib/loc.cmx lib/cErrors.cmx \
    parsing/ppextend.cmi
parsing/ppextend.cmi : lib/pp.cmi parsing/notation_gram.cmo lib/loc.cmi \
    interp/constrexpr.cmo
parsing/tok.cmo : parsing/tok.cmi
parsing/tok.cmx : parsing/tok.cmi
parsing/tok.cmi :
pretyping/arguments_renaming.cmo : lib/util.cmi kernel/typeops.cmi \
    kernel/term.cmi library/summary.cmi kernel/names.cmi \
    library/libobject.cmi library/lib.cmi pretyping/inductiveops.cmi \
    library/globnames.cmi kernel/environ.cmi kernel/context.cmi \
    kernel/constr.cmi pretyping/arguments_renaming.cmi
pretyping/arguments_renaming.cmx : lib/util.cmx kernel/typeops.cmx \
    kernel/term.cmx library/summary.cmx kernel/names.cmx \
    library/libobject.cmx library/lib.cmx pretyping/inductiveops.cmx \
    library/globnames.cmx kernel/environ.cmx kernel/context.cmx \
    kernel/constr.cmx pretyping/arguments_renaming.cmi
pretyping/arguments_renaming.cmi : kernel/names.cmi kernel/environ.cmi \
    kernel/constr.cmi
pretyping/cases.cmo : kernel/vars.cmi lib/util.cmi pretyping/typing.cmi \
    kernel/type_errors.cmi engine/termops.cmi pretyping/tacred.cmi \
    pretyping/retyping.cmi pretyping/reductionops.cmi kernel/reduction.cmi \
    pretyping/program.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    clib/option.cmi kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    pretyping/ltac_pretype.cmo lib/loc.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi library/globnames.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi lib/flags.cmi \
    engine/evd.cmi engine/evarutil.cmi pretyping/evarsolve.cmi \
    pretyping/evardefine.cmi pretyping/evarconv.cmi engine/evar_kinds.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/declarations.cmo \
    lib/dAst.cmi kernel/context.cmi kernel/constr.cmi pretyping/coercion.cmi \
    lib/cErrors.cmi lib/cAst.cmi pretyping/cases.cmi
pretyping/cases.cmx : kernel/vars.cmx lib/util.cmx pretyping/typing.cmx \
    kernel/type_errors.cmx engine/termops.cmx pretyping/tacred.cmx \
    pretyping/retyping.cmx pretyping/reductionops.cmx kernel/reduction.cmx \
    pretyping/program.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    clib/option.cmx kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    pretyping/ltac_pretype.cmx lib/loc.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx library/globnames.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx lib/flags.cmx \
    engine/evd.cmx engine/evarutil.cmx pretyping/evarsolve.cmx \
    pretyping/evardefine.cmx pretyping/evarconv.cmx engine/evar_kinds.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/declarations.cmx \
    lib/dAst.cmx kernel/context.cmx kernel/constr.cmx pretyping/coercion.cmx \
    lib/cErrors.cmx lib/cAst.cmx pretyping/cases.cmi
pretyping/cases.cmi : kernel/names.cmi pretyping/ltac_pretype.cmo \
    lib/loc.cmi pretyping/inductiveops.cmi pretyping/glob_term.cmo \
    engine/evd.cmi pretyping/evardefine.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi
pretyping/cbv.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/term.cmi pretyping/reductionops.cmi lib/pp.cmi kernel/names.cmi \
    clib/int.cmi library/goptions.cmi lib/feedback.cmi engine/evd.cmi \
    kernel/esubst.cmi engine/eConstr.cmi kernel/constr.cmi \
    kernel/cClosure.cmi pretyping/cbv.cmi
pretyping/cbv.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/term.cmx pretyping/reductionops.cmx lib/pp.cmx kernel/names.cmx \
    clib/int.cmx library/goptions.cmx lib/feedback.cmx engine/evd.cmx \
    kernel/esubst.cmx engine/eConstr.cmx kernel/constr.cmx \
    kernel/cClosure.cmx pretyping/cbv.cmi
pretyping/cbv.cmi : kernel/univ.cmi kernel/names.cmi engine/evd.cmi \
    kernel/esubst.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi \
    kernel/cClosure.cmi
pretyping/classops.cmo : lib/util.cmi pretyping/tacred.cmi \
    library/summary.cmi pretyping/reductionops.cmi pretyping/recordops.cmi \
    lib/pp.cmi clib/option.cmi library/nametab.cmi kernel/names.cmi \
    kernel/mod_subst.cmi library/libobject.cmi library/libnames.cmi \
    library/lib.cmi clib/int.cmi pretyping/inductiveops.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    lib/flags.cmi lib/feedback.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi lib/cErrors.cmi \
    pretyping/classops.cmi
pretyping/classops.cmx : lib/util.cmx pretyping/tacred.cmx \
    library/summary.cmx pretyping/reductionops.cmx pretyping/recordops.cmx \
    lib/pp.cmx clib/option.cmx library/nametab.cmx kernel/names.cmx \
    kernel/mod_subst.cmx library/libobject.cmx library/libnames.cmx \
    library/lib.cmx clib/int.cmx pretyping/inductiveops.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    lib/flags.cmx lib/feedback.cmx engine/evd.cmx kernel/environ.cmx \
    engine/eConstr.cmx kernel/constr.cmx lib/cErrors.cmx \
    pretyping/classops.cmi
pretyping/classops.cmi : lib/pp.cmi kernel/names.cmi kernel/mod_subst.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi
pretyping/coercion.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    pretyping/typing.cmi pretyping/typeclasses.cmi engine/termops.cmi \
    kernel/term.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    pretyping/program.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    clib/option.cmi library/nametab.cmi kernel/names.cmi engine/namegen.cmi \
    lib/loc.cmi clib/int.cmi pretyping/heads.cmi library/goptions.cmi \
    library/globnames.cmi pretyping/glob_term.cmo lib/flags.cmi \
    engine/evd.cmi engine/evarutil.cmi pretyping/evardefine.cmi \
    pretyping/evarconv.cmi engine/evar_kinds.cmi kernel/environ.cmi \
    engine/eConstr.cmi lib/dAst.cmi kernel/context.cmi kernel/constr.cmi \
    pretyping/classops.cmi lib/cWarnings.cmi lib/cErrors.cmi \
    pretyping/coercion.cmi
pretyping/coercion.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    pretyping/typing.cmx pretyping/typeclasses.cmx engine/termops.cmx \
    kernel/term.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    pretyping/program.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    clib/option.cmx library/nametab.cmx kernel/names.cmx engine/namegen.cmx \
    lib/loc.cmx clib/int.cmx pretyping/heads.cmx library/goptions.cmx \
    library/globnames.cmx pretyping/glob_term.cmx lib/flags.cmx \
    engine/evd.cmx engine/evarutil.cmx pretyping/evardefine.cmx \
    pretyping/evarconv.cmx engine/evar_kinds.cmx kernel/environ.cmx \
    engine/eConstr.cmx lib/dAst.cmx kernel/context.cmx kernel/constr.cmx \
    pretyping/classops.cmx lib/cWarnings.cmx lib/cErrors.cmx \
    pretyping/coercion.cmi
pretyping/coercion.cmi : kernel/names.cmi lib/loc.cmi \
    pretyping/glob_term.cmo engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi
pretyping/constr_matching.cmo : kernel/vars.cmi lib/util.cmi \
    engine/termops.cmi kernel/term.cmi pretyping/retyping.cmi lib/pp.cmi \
    pretyping/patternops.cmi pretyping/pattern.cmo clib/option.cmi \
    kernel/names.cmi engine/namegen.cmi pretyping/ltac_pretype.cmo \
    clib/int.cmi clib/iStream.cmi library/globnames.cmi \
    pretyping/glob_term.cmo pretyping/glob_ops.cmi kernel/evar.cmi \
    engine/eConstr.cmi kernel/context.cmi kernel/constr.cmi lib/cWarnings.cmi \
    clib/cList.cmi lib/cErrors.cmi pretyping/constr_matching.cmi
pretyping/constr_matching.cmx : kernel/vars.cmx lib/util.cmx \
    engine/termops.cmx kernel/term.cmx pretyping/retyping.cmx lib/pp.cmx \
    pretyping/patternops.cmx pretyping/pattern.cmx clib/option.cmx \
    kernel/names.cmx engine/namegen.cmx pretyping/ltac_pretype.cmx \
    clib/int.cmx clib/iStream.cmx library/globnames.cmx \
    pretyping/glob_term.cmx pretyping/glob_ops.cmx kernel/evar.cmx \
    engine/eConstr.cmx kernel/context.cmx kernel/constr.cmx lib/cWarnings.cmx \
    clib/cList.cmx lib/cErrors.cmx pretyping/constr_matching.cmi
pretyping/constr_matching.cmi : pretyping/pattern.cmo kernel/names.cmi \
    pretyping/ltac_pretype.cmo clib/iStream.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi
pretyping/detyping.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    engine/termops.cmi kernel/term.cmi pretyping/retyping.cmi lib/pp.cmi \
    pretyping/pattern.cmo clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    kernel/mod_subst.cmi pretyping/ltac_pretype.cmo library/libnames.cmi \
    clib/int.cmi pretyping/inductiveops.cmi lib/hook.cmi library/goptions.cmi \
    library/globnames.cmi library/global.cmi pretyping/glob_term.cmo \
    pretyping/glob_ops.cmi lib/flags.cmi lib/feedback.cmi engine/evd.cmi \
    engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi library/decl_kinds.cmo lib/dAst.cmi kernel/context.cmi \
    pretyping/constr_matching.cmi kernel/constr.cmi lib/cErrors.cmi \
    lib/cAst.cmi pretyping/detyping.cmi
pretyping/detyping.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    engine/termops.cmx kernel/term.cmx pretyping/retyping.cmx lib/pp.cmx \
    pretyping/pattern.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    kernel/mod_subst.cmx pretyping/ltac_pretype.cmx library/libnames.cmx \
    clib/int.cmx pretyping/inductiveops.cmx lib/hook.cmx library/goptions.cmx \
    library/globnames.cmx library/global.cmx pretyping/glob_term.cmx \
    pretyping/glob_ops.cmx lib/flags.cmx lib/feedback.cmx engine/evd.cmx \
    engine/evar_kinds.cmx kernel/evar.cmx kernel/environ.cmx \
    engine/eConstr.cmx library/decl_kinds.cmx lib/dAst.cmx kernel/context.cmx \
    pretyping/constr_matching.cmx kernel/constr.cmx lib/cErrors.cmx \
    lib/cAst.cmx pretyping/detyping.cmi
pretyping/detyping.cmi : engine/termops.cmi kernel/sorts.cmi lib/pp.cmi \
    pretyping/pattern.cmo kernel/names.cmi kernel/mod_subst.cmi \
    pretyping/ltac_pretype.cmo lib/loc.cmi library/libnames.cmi lib/hook.cmi \
    library/goptions.cmi pretyping/glob_term.cmo lib/genarg.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo
pretyping/evarconv.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi engine/termops.cmi kernel/sorts.cmi \
    pretyping/retyping.cmi pretyping/reductionops.cmi kernel/reduction.cmi \
    pretyping/recordops.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    clib/option.cmi kernel/names.cmi engine/nameops.cmi pretyping/locus.cmo \
    lib/loc.cmi clib/int.cmi pretyping/inductiveops.cmi lib/hook.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    lib/flags.cmi lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarsolve.cmi pretyping/evardefine.cmi engine/evar_kinds.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declarations.cmo library/coqlib.cmi kernel/conv_oracle.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cProfile.cmi lib/cErrors.cmi \
    kernel/cClosure.cmi pretyping/evarconv.cmi
pretyping/evarconv.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx engine/termops.cmx kernel/sorts.cmx \
    pretyping/retyping.cmx pretyping/reductionops.cmx kernel/reduction.cmx \
    pretyping/recordops.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    clib/option.cmx kernel/names.cmx engine/nameops.cmx pretyping/locus.cmx \
    lib/loc.cmx clib/int.cmx pretyping/inductiveops.cmx lib/hook.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    lib/flags.cmx lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarsolve.cmx pretyping/evardefine.cmx engine/evar_kinds.cmx \
    kernel/evar.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declarations.cmx library/coqlib.cmx kernel/conv_oracle.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cProfile.cmx lib/cErrors.cmx \
    kernel/cClosure.cmx pretyping/evarconv.cmi
pretyping/evarconv.cmi : kernel/univ.cmi pretyping/reductionops.cmi \
    pretyping/pretype_errors.cmi kernel/names.cmi pretyping/locus.cmo \
    engine/evd.cmi pretyping/evarsolve.cmi kernel/environ.cmi \
    engine/eConstr.cmi
pretyping/evardefine.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    engine/termops.cmi kernel/sorts.cmi pretyping/reductionops.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/namegen.cmi engine/evd.cmi engine/evarutil.cmi \
    engine/evar_kinds.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/context.cmi kernel/constr.cmi pretyping/evardefine.cmi
pretyping/evardefine.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    engine/termops.cmx kernel/sorts.cmx pretyping/reductionops.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/namegen.cmx engine/evd.cmx engine/evarutil.cmx \
    engine/evar_kinds.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/context.cmx kernel/constr.cmx pretyping/evardefine.cmi
pretyping/evardefine.cmi : kernel/sorts.cmi lib/pp.cmi kernel/names.cmi \
    lib/loc.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi
pretyping/evarsolve.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    engine/termops.cmi kernel/sorts.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/namegen.cmi clib/int.cmi pretyping/inductiveops.cmi \
    library/global.cmi engine/evd.cmi engine/evarutil.cmi \
    engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi pretyping/evarsolve.cmi
pretyping/evarsolve.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    engine/termops.cmx kernel/sorts.cmx pretyping/retyping.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/namegen.cmx clib/int.cmx pretyping/inductiveops.cmx \
    library/global.cmx engine/evd.cmx engine/evarutil.cmx \
    engine/evar_kinds.cmx kernel/evar.cmx kernel/environ.cmx \
    engine/eConstr.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx pretyping/evarsolve.cmi
pretyping/evarsolve.cmi : pretyping/pretype_errors.cmi engine/evd.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi
pretyping/find_subterm.cmo : kernel/vars.cmi lib/util.cmi engine/termops.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo clib/int.cmi engine/evd.cmi \
    engine/eConstr.cmi kernel/context.cmi lib/cErrors.cmi \
    pretyping/find_subterm.cmi
pretyping/find_subterm.cmx : kernel/vars.cmx lib/util.cmx engine/termops.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx clib/int.cmx engine/evd.cmx \
    engine/eConstr.cmx kernel/context.cmx lib/cErrors.cmx \
    pretyping/find_subterm.cmi
pretyping/find_subterm.cmi : pretyping/pretype_errors.cmi \
    pretyping/locus.cmo engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi
pretyping/geninterp.cmo : clib/store.cmi lib/pp.cmi clib/option.cmi \
    kernel/names.cmi lib/genarg.cmi engine/ftactic.cmi clib/dyn.cmi \
    pretyping/geninterp.cmi
pretyping/geninterp.cmx : clib/store.cmx lib/pp.cmx clib/option.cmx \
    kernel/names.cmx lib/genarg.cmx engine/ftactic.cmx clib/dyn.cmx \
    pretyping/geninterp.cmi
pretyping/geninterp.cmi : clib/store.cmi lib/pp.cmi kernel/names.cmi \
    lib/genarg.cmi engine/ftactic.cmi clib/dyn.cmi clib/cSig.cmi
pretyping/glob_ops.cmo : lib/util.cmi kernel/term.cmi lib/pp.cmi \
    clib/option.cmi library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi pretyping/ltac_pretype.cmo library/libnames.cmi \
    clib/int.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo engine/evar_kinds.cmi kernel/declarations.cmo \
    library/decl_kinds.cmo lib/dAst.cmi kernel/context.cmi kernel/constr.cmi \
    lib/cWarnings.cmi clib/cList.cmi lib/cErrors.cmi lib/cAst.cmi \
    pretyping/glob_ops.cmi
pretyping/glob_ops.cmx : lib/util.cmx kernel/term.cmx lib/pp.cmx \
    clib/option.cmx library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx pretyping/ltac_pretype.cmx library/libnames.cmx \
    clib/int.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx engine/evar_kinds.cmx kernel/declarations.cmx \
    library/decl_kinds.cmx lib/dAst.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cWarnings.cmx clib/cList.cmx lib/cErrors.cmx lib/cAst.cmx \
    pretyping/glob_ops.cmi
pretyping/glob_ops.cmi : kernel/names.cmi pretyping/ltac_pretype.cmo \
    lib/loc.cmi pretyping/glob_term.cmo
pretyping/glob_term.cmo : kernel/univ.cmi kernel/names.cmi \
    engine/namegen.cmi library/libnames.cmi lib/genarg.cmi \
    engine/evar_kinds.cmi library/decl_kinds.cmo lib/dAst.cmi \
    kernel/constr.cmi lib/cAst.cmi
pretyping/glob_term.cmx : kernel/univ.cmx kernel/names.cmx \
    engine/namegen.cmx library/libnames.cmx lib/genarg.cmx \
    engine/evar_kinds.cmx library/decl_kinds.cmx lib/dAst.cmx \
    kernel/constr.cmx lib/cAst.cmx
pretyping/heads.cmo : kernel/vars.cmi lib/util.cmi library/summary.cmi \
    kernel/reduction.cmi pretyping/recordops.cmi lib/pp.cmi kernel/names.cmi \
    kernel/mod_subst.cmi library/libobject.cmi library/lib.cmi \
    library/globnames.cmi library/global.cmi kernel/environ.cmi \
    library/decls.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi pretyping/heads.cmi
pretyping/heads.cmx : kernel/vars.cmx lib/util.cmx library/summary.cmx \
    kernel/reduction.cmx pretyping/recordops.cmx lib/pp.cmx kernel/names.cmx \
    kernel/mod_subst.cmx library/libobject.cmx library/lib.cmx \
    library/globnames.cmx library/global.cmx kernel/environ.cmx \
    library/decls.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx pretyping/heads.cmi
pretyping/heads.cmi : kernel/names.cmi kernel/environ.cmi kernel/constr.cmi
pretyping/indrec.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    engine/termops.cmi kernel/term.cmi kernel/sorts.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi lib/pp.cmi \
    clib/option.cmi library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi library/libnames.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi library/globnames.cmi \
    library/global.cmi engine/evd.cmi engine/evarutil.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/declareops.cmi kernel/declarations.cmo \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi pretyping/indrec.cmi
pretyping/indrec.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    engine/termops.cmx kernel/term.cmx kernel/sorts.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx lib/pp.cmx \
    clib/option.cmx library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx library/libnames.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx library/globnames.cmx \
    library/global.cmx engine/evd.cmx engine/evarutil.cmx kernel/environ.cmx \
    engine/eConstr.cmx kernel/declareops.cmx kernel/declarations.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx pretyping/indrec.cmi
pretyping/indrec.cmi : kernel/sorts.cmi kernel/names.cmi engine/evd.cmi \
    kernel/environ.cmi kernel/constr.cmi
pretyping/inductiveops.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/typeops.cmi engine/termops.cmi kernel/term.cmi kernel/sorts.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi lib/pp.cmi \
    kernel/names.cmi engine/namegen.cmi clib/int.cmi kernel/inductive.cmi \
    library/global.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi pretyping/inductiveops.cmi
pretyping/inductiveops.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/typeops.cmx engine/termops.cmx kernel/term.cmx kernel/sorts.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx lib/pp.cmx \
    kernel/names.cmx engine/namegen.cmx clib/int.cmx kernel/inductive.cmx \
    library/global.cmx engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx pretyping/inductiveops.cmi
pretyping/inductiveops.cmi : kernel/univ.cmi kernel/sorts.cmi \
    kernel/names.cmi kernel/inductive.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/declarations.cmo kernel/constr.cmi
pretyping/inferCumulativity.cmo : lib/util.cmi kernel/univ.cmi \
    kernel/typeops.cmi kernel/sorts.cmi kernel/reduction.cmi kernel/names.cmi \
    clib/int.cmi kernel/esubst.cmi kernel/environ.cmi kernel/entries.cmo \
    kernel/declarations.cmo lib/control.cmi kernel/context.cmi \
    kernel/constr.cmi kernel/cClosure.cmi pretyping/inferCumulativity.cmi
pretyping/inferCumulativity.cmx : lib/util.cmx kernel/univ.cmx \
    kernel/typeops.cmx kernel/sorts.cmx kernel/reduction.cmx kernel/names.cmx \
    clib/int.cmx kernel/esubst.cmx kernel/environ.cmx kernel/entries.cmx \
    kernel/declarations.cmx lib/control.cmx kernel/context.cmx \
    kernel/constr.cmx kernel/cClosure.cmx pretyping/inferCumulativity.cmi
pretyping/inferCumulativity.cmi : kernel/environ.cmi kernel/entries.cmo
pretyping/locus.cmo : kernel/names.cmi
pretyping/locus.cmx : kernel/names.cmx
pretyping/locusops.cmo : lib/pp.cmi clib/option.cmi kernel/names.cmi \
    pretyping/locus.cmo clib/int.cmi lib/cErrors.cmi pretyping/locusops.cmi
pretyping/locusops.cmx : lib/pp.cmx clib/option.cmx kernel/names.cmx \
    pretyping/locus.cmx clib/int.cmx lib/cErrors.cmx pretyping/locusops.cmi
pretyping/locusops.cmi : kernel/names.cmi pretyping/locus.cmo
pretyping/ltac_pretype.cmo : kernel/names.cmi pretyping/glob_term.cmo \
    pretyping/geninterp.cmi engine/eConstr.cmi
pretyping/ltac_pretype.cmx : kernel/names.cmx pretyping/glob_term.cmx \
    pretyping/geninterp.cmx engine/eConstr.cmx
pretyping/nativenorm.cmo : kernel/vars.cmi lib/util.cmi kernel/typeops.cmi \
    engine/termops.cmi kernel/term.cmi kernel/retroknowledge.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi lib/pp.cmi \
    kernel/nativevalues.cmi kernel/nativelib.cmi kernel/nativelambda.cmi \
    kernel/nativeconv.cmi kernel/nativecode.cmi kernel/names.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declareops.cmi kernel/declarations.cmo config/coq_config.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    pretyping/nativenorm.cmi
pretyping/nativenorm.cmx : kernel/vars.cmx lib/util.cmx kernel/typeops.cmx \
    engine/termops.cmx kernel/term.cmx kernel/retroknowledge.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx lib/pp.cmx \
    kernel/nativevalues.cmx kernel/nativelib.cmx kernel/nativelambda.cmx \
    kernel/nativeconv.cmx kernel/nativecode.cmx kernel/names.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declareops.cmx kernel/declarations.cmx config/coq_config.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    pretyping/nativenorm.cmi
pretyping/nativenorm.cmi : engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi
pretyping/pattern.cmo : kernel/names.cmi pretyping/glob_term.cmo \
    kernel/evar.cmi kernel/constr.cmi
pretyping/pattern.cmx : kernel/names.cmx pretyping/glob_term.cmx \
    kernel/evar.cmx kernel/constr.cmx
pretyping/patternops.cmo : kernel/vars.cmi lib/util.cmi kernel/term.cmi \
    pretyping/retyping.cmi lib/pp.cmi pretyping/pattern.cmo clib/option.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    kernel/mod_subst.cmi clib/int.cmi library/globnames.cmi \
    library/global.cmi pretyping/glob_term.cmo pretyping/glob_ops.cmi \
    engine/evd.cmi engine/evarutil.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi library/decl_kinds.cmo lib/dAst.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cWarnings.cmi lib/cErrors.cmi \
    lib/cAst.cmi pretyping/patternops.cmi
pretyping/patternops.cmx : kernel/vars.cmx lib/util.cmx kernel/term.cmx \
    pretyping/retyping.cmx lib/pp.cmx pretyping/pattern.cmx clib/option.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    kernel/mod_subst.cmx clib/int.cmx library/globnames.cmx \
    library/global.cmx pretyping/glob_term.cmx pretyping/glob_ops.cmx \
    engine/evd.cmx engine/evarutil.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    kernel/environ.cmx engine/eConstr.cmx library/decl_kinds.cmx lib/dAst.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cWarnings.cmx lib/cErrors.cmx \
    lib/cAst.cmx pretyping/patternops.cmi
pretyping/patternops.cmi : pretyping/pattern.cmo kernel/names.cmi \
    kernel/mod_subst.cmi pretyping/ltac_pretype.cmo pretyping/glob_term.cmo \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi
pretyping/pretype_errors.cmo : kernel/univ.cmi kernel/type_errors.cmi \
    library/nametab.cmi kernel/names.cmi pretyping/locus.cmo lib/loc.cmi \
    engine/evd.cmi engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi lib/cErrors.cmi pretyping/pretype_errors.cmi
pretyping/pretype_errors.cmx : kernel/univ.cmx kernel/type_errors.cmx \
    library/nametab.cmx kernel/names.cmx pretyping/locus.cmx lib/loc.cmx \
    engine/evd.cmx engine/evar_kinds.cmx kernel/evar.cmx kernel/environ.cmx \
    engine/eConstr.cmx lib/cErrors.cmx pretyping/pretype_errors.cmi
pretyping/pretype_errors.cmi : kernel/univ.cmi kernel/type_errors.cmi \
    kernel/sorts.cmi kernel/names.cmi pretyping/locus.cmo lib/loc.cmi \
    engine/evd.cmi engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi
pretyping/pretyping.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/uGraph.cmi pretyping/typing.cmi pretyping/typeclasses.cmi \
    kernel/type_errors.cmi engine/termops.cmi kernel/term.cmi \
    pretyping/retyping.cmi pretyping/reductionops.cmi pretyping/recordops.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi clib/option.cmi \
    pretyping/nativenorm.cmi library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi pretyping/ltac_pretype.cmo \
    lib/loc.cmi library/libnames.cmi clib/int.cmi pretyping/inductiveops.cmi \
    kernel/inductive.cmi library/goptions.cmi library/globnames.cmi \
    library/global.cmi pretyping/glob_term.cmo pretyping/glob_ops.cmi \
    pretyping/geninterp.cmi lib/genarg.cmi lib/flags.cmi engine/evd.cmi \
    engine/evarutil.cmi pretyping/evarsolve.cmi pretyping/evardefine.cmi \
    pretyping/evarconv.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/declarations.cmo \
    lib/dAst.cmi kernel/context.cmi kernel/constr.cmi pretyping/coercion.cmi \
    pretyping/cases.cmi lib/cErrors.cmi lib/cAst.cmi pretyping/pretyping.cmi
pretyping/pretyping.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/uGraph.cmx pretyping/typing.cmx pretyping/typeclasses.cmx \
    kernel/type_errors.cmx engine/termops.cmx kernel/term.cmx \
    pretyping/retyping.cmx pretyping/reductionops.cmx pretyping/recordops.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx clib/option.cmx \
    pretyping/nativenorm.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx pretyping/ltac_pretype.cmx \
    lib/loc.cmx library/libnames.cmx clib/int.cmx pretyping/inductiveops.cmx \
    kernel/inductive.cmx library/goptions.cmx library/globnames.cmx \
    library/global.cmx pretyping/glob_term.cmx pretyping/glob_ops.cmx \
    pretyping/geninterp.cmx lib/genarg.cmx lib/flags.cmx engine/evd.cmx \
    engine/evarutil.cmx pretyping/evarsolve.cmx pretyping/evardefine.cmx \
    pretyping/evarconv.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/declarations.cmx \
    lib/dAst.cmx kernel/context.cmx kernel/constr.cmx pretyping/coercion.cmx \
    pretyping/cases.cmx lib/cErrors.cmx lib/cAst.cmx pretyping/pretyping.cmi
pretyping/pretyping.cmi : kernel/univ.cmi pretyping/ltac_pretype.cmo \
    lib/loc.cmi pretyping/glob_term.cmo lib/genarg.cmi engine/evd.cmi \
    pretyping/evardefine.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi
pretyping/program.cmo : lib/util.cmi library/goptions.cmi \
    engine/evarutil.cmi engine/eConstr.cmi library/coqlib.cmi lib/cErrors.cmi \
    pretyping/program.cmi
pretyping/program.cmx : lib/util.cmx library/goptions.cmx \
    engine/evarutil.cmx engine/eConstr.cmx library/coqlib.cmx lib/cErrors.cmx \
    pretyping/program.cmi
pretyping/program.cmi : kernel/names.cmi engine/evd.cmi engine/eConstr.cmi
pretyping/recordops.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/typeops.cmi engine/termops.cmi library/summary.cmi \
    kernel/sorts.cmi pretyping/reductionops.cmi lib/pp.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi kernel/mod_subst.cmi \
    library/libobject.cmi library/lib.cmi clib/int.cmi kernel/inductive.cmi \
    library/globnames.cmi library/global.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/declarations.cmo \
    kernel/constr.cmi lib/cWarnings.cmi lib/cErrors.cmi \
    pretyping/recordops.cmi
pretyping/recordops.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/typeops.cmx engine/termops.cmx library/summary.cmx \
    kernel/sorts.cmx pretyping/reductionops.cmx lib/pp.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx kernel/mod_subst.cmx \
    library/libobject.cmx library/lib.cmx clib/int.cmx kernel/inductive.cmx \
    library/globnames.cmx library/global.cmx engine/evd.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/declarations.cmx \
    kernel/constr.cmx lib/cWarnings.cmx lib/cErrors.cmx \
    pretyping/recordops.cmi
pretyping/recordops.cmi : kernel/univ.cmi kernel/sorts.cmi \
    pretyping/reductionops.cmi lib/pp.cmi kernel/names.cmi engine/evd.cmi \
    kernel/environ.cmi kernel/constr.cmi
pretyping/reductionops.cmo : kernel/vars.cmi lib/util.cmi \
    engine/univProblem.cmi engine/univGen.cmi kernel/univ.cmi \
    engine/uState.cmi engine/termops.cmi library/summary.cmi \
    kernel/reduction.cmi lib/pp.cmi clib/option.cmi library/nametab.cmi \
    kernel/names.cmi kernel/mod_subst.cmi library/libobject.cmi \
    library/lib.cmi clib/int.cmi library/goptions.cmi library/globnames.cmi \
    lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/conv_oracle.cmi kernel/context.cmi \
    kernel/constr.cmi clib/cList.cmi lib/cErrors.cmi kernel/cClosure.cmi \
    clib/cArray.cmi pretyping/reductionops.cmi
pretyping/reductionops.cmx : kernel/vars.cmx lib/util.cmx \
    engine/univProblem.cmx engine/univGen.cmx kernel/univ.cmx \
    engine/uState.cmx engine/termops.cmx library/summary.cmx \
    kernel/reduction.cmx lib/pp.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx kernel/mod_subst.cmx library/libobject.cmx \
    library/lib.cmx clib/int.cmx library/goptions.cmx library/globnames.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx kernel/environ.cmx \
    engine/eConstr.cmx kernel/conv_oracle.cmx kernel/context.cmx \
    kernel/constr.cmx clib/cList.cmx lib/cErrors.cmx kernel/cClosure.cmx \
    clib/cArray.cmx pretyping/reductionops.cmi
pretyping/reductionops.cmi : kernel/univ.cmi kernel/reduction.cmi lib/pp.cmi \
    kernel/names.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/constr.cmi kernel/cClosure.cmi
pretyping/retyping.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/typeops.cmi engine/termops.cmi kernel/term.cmi kernel/sorts.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi lib/pp.cmi \
    kernel/names.cmi pretyping/inductiveops.cmi kernel/inductive.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi pretyping/arguments_renaming.cmi \
    pretyping/retyping.cmi
pretyping/retyping.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/typeops.cmx engine/termops.cmx kernel/term.cmx kernel/sorts.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx lib/pp.cmx \
    kernel/names.cmx pretyping/inductiveops.cmx kernel/inductive.cmx \
    engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx pretyping/arguments_renaming.cmx \
    pretyping/retyping.cmi
pretyping/retyping.cmi : kernel/sorts.cmi lib/pp.cmi kernel/names.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi
pretyping/tacred.cmo : kernel/vars.cmi lib/util.cmi pretyping/typing.cmi \
    kernel/type_errors.cmi engine/termops.cmi library/summary.cmi \
    pretyping/retyping.cmi pretyping/reductionops.cmi lib/pp.cmi \
    pretyping/patternops.cmi clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/namegen.cmi kernel/mod_subst.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo library/libnames.cmi \
    clib/int.cmi kernel/inductive.cmi library/globnames.cmi lib/flags.cmi \
    pretyping/find_subterm.cmi engine/evd.cmi engine/evarutil.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declarations.cmo kernel/context.cmi pretyping/constr_matching.cmi \
    kernel/constr.cmi pretyping/cbv.cmi lib/cProfile.cmi lib/cErrors.cmi \
    kernel/cClosure.cmi pretyping/tacred.cmi
pretyping/tacred.cmx : kernel/vars.cmx lib/util.cmx pretyping/typing.cmx \
    kernel/type_errors.cmx engine/termops.cmx library/summary.cmx \
    pretyping/retyping.cmx pretyping/reductionops.cmx lib/pp.cmx \
    pretyping/patternops.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/namegen.cmx kernel/mod_subst.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx library/libnames.cmx \
    clib/int.cmx kernel/inductive.cmx library/globnames.cmx lib/flags.cmx \
    pretyping/find_subterm.cmx engine/evd.cmx engine/evarutil.cmx \
    kernel/evar.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declarations.cmx kernel/context.cmx pretyping/constr_matching.cmx \
    kernel/constr.cmx pretyping/cbv.cmx lib/cProfile.cmx lib/cErrors.cmx \
    kernel/cClosure.cmx pretyping/tacred.cmi
pretyping/tacred.cmi : kernel/univ.cmi kernel/type_errors.cmi \
    pretyping/reductionops.cmi pretyping/pattern.cmo kernel/names.cmi \
    pretyping/ltac_pretype.cmo pretyping/locus.cmo engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/cClosure.cmi
pretyping/typeclasses.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi pretyping/typeclasses_errors.cmi engine/termops.cmi \
    kernel/term.cmi pretyping/tacred.cmi library/summary.cmi clib/store.cmi \
    pretyping/retyping.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    lib/pp.cmi pretyping/pattern.cmo clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi kernel/mod_subst.cmi \
    library/libobject.cmi library/lib.cmi lib/hook.cmi library/goptions.cmi \
    library/globnames.cmi library/global.cmi engine/evd.cmi \
    engine/evar_kinds.cmi kernel/evar.cmi engine/eConstr.cmi \
    library/decls.cmi library/decl_kinds.cmo kernel/cooking.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi \
    pretyping/typeclasses.cmi
pretyping/typeclasses.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx pretyping/typeclasses_errors.cmx engine/termops.cmx \
    kernel/term.cmx pretyping/tacred.cmx library/summary.cmx clib/store.cmx \
    pretyping/retyping.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    lib/pp.cmx pretyping/pattern.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx kernel/mod_subst.cmx \
    library/libobject.cmx library/lib.cmx lib/hook.cmx library/goptions.cmx \
    library/globnames.cmx library/global.cmx engine/evd.cmx \
    engine/evar_kinds.cmx kernel/evar.cmx engine/eConstr.cmx \
    library/decls.cmx library/decl_kinds.cmx kernel/cooking.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx \
    pretyping/typeclasses.cmi
pretyping/typeclasses.cmi : kernel/univ.cmi pretyping/pattern.cmo \
    kernel/names.cmi lib/hook.cmi library/globnames.cmi engine/evd.cmi \
    engine/evar_kinds.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi library/decl_kinds.cmo kernel/constr.cmi
pretyping/typeclasses_errors.cmo : kernel/names.cmi kernel/environ.cmi \
    engine/eConstr.cmi pretyping/typeclasses_errors.cmi
pretyping/typeclasses_errors.cmx : kernel/names.cmx kernel/environ.cmx \
    engine/eConstr.cmx pretyping/typeclasses_errors.cmi
pretyping/typeclasses_errors.cmi : kernel/names.cmi kernel/environ.cmi \
    engine/eConstr.cmi
pretyping/typing.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/typeops.cmi kernel/type_errors.cmi engine/termops.cmi \
    kernel/term.cmi kernel/sorts.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    engine/nameops.cmi clib/int.cmi pretyping/inductiveops.cmi \
    kernel/inductive.cmi library/global.cmi engine/evd.cmi \
    engine/evarutil.cmi pretyping/evarsolve.cmi pretyping/evardefine.cmi \
    pretyping/evarconv.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declarations.cmo kernel/context.cmi kernel/constr.cmi \
    lib/cErrors.cmi pretyping/arguments_renaming.cmi pretyping/typing.cmi
pretyping/typing.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/typeops.cmx kernel/type_errors.cmx engine/termops.cmx \
    kernel/term.cmx kernel/sorts.cmx pretyping/retyping.cmx \
    pretyping/reductionops.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    engine/nameops.cmx clib/int.cmx pretyping/inductiveops.cmx \
    kernel/inductive.cmx library/global.cmx engine/evd.cmx \
    engine/evarutil.cmx pretyping/evarsolve.cmx pretyping/evardefine.cmx \
    pretyping/evarconv.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declarations.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cErrors.cmx pretyping/arguments_renaming.cmx pretyping/typing.cmi
pretyping/typing.cmi : kernel/sorts.cmi kernel/names.cmi lib/loc.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi
pretyping/unification.cmo : kernel/vars.cmi lib/util.cmi \
    engine/univProblem.cmi kernel/univ.cmi pretyping/typing.cmi \
    pretyping/typeclasses.cmi kernel/type_errors.cmi engine/termops.cmi \
    pretyping/tacred.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    kernel/reduction.cmi pretyping/recordops.cmi pretyping/pretyping.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/namegen.cmi pretyping/locusops.cmi pretyping/locus.cmo lib/loc.cmi \
    library/keys.cmi clib/int.cmi library/goptions.cmi library/global.cmi \
    lib/flags.cmi pretyping/find_subterm.cmi lib/feedback.cmi engine/evd.cmi \
    engine/evarutil.cmi pretyping/evarsolve.cmi pretyping/evardefine.cmi \
    pretyping/evarconv.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/declarations.cmo \
    kernel/conv_oracle.cmi kernel/context.cmi kernel/constr.cmi \
    pretyping/coercion.cmi lib/cProfile.cmi lib/cErrors.cmi \
    kernel/cClosure.cmi pretyping/unification.cmi
pretyping/unification.cmx : kernel/vars.cmx lib/util.cmx \
    engine/univProblem.cmx kernel/univ.cmx pretyping/typing.cmx \
    pretyping/typeclasses.cmx kernel/type_errors.cmx engine/termops.cmx \
    pretyping/tacred.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    kernel/reduction.cmx pretyping/recordops.cmx pretyping/pretyping.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/namegen.cmx pretyping/locusops.cmx pretyping/locus.cmx lib/loc.cmx \
    library/keys.cmx clib/int.cmx library/goptions.cmx library/global.cmx \
    lib/flags.cmx pretyping/find_subterm.cmx lib/feedback.cmx engine/evd.cmx \
    engine/evarutil.cmx pretyping/evarsolve.cmx pretyping/evardefine.cmx \
    pretyping/evarconv.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/declarations.cmx \
    kernel/conv_oracle.cmx kernel/context.cmx kernel/constr.cmx \
    pretyping/coercion.cmx lib/cProfile.cmx lib/cErrors.cmx \
    kernel/cClosure.cmx pretyping/unification.cmi
pretyping/unification.cmi : pretyping/pretyping.cmi kernel/names.cmi \
    pretyping/locus.cmo engine/evd.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi
pretyping/vnorm.cmo : kernel/vmvalues.cmi kernel/vm.cmi kernel/vconv.cmi \
    kernel/vars.cmi lib/util.cmi kernel/univ.cmi kernel/typeops.cmi \
    engine/termops.cmi kernel/term.cmi kernel/retroknowledge.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi lib/pp.cmi \
    kernel/names.cmi clib/int.cmi pretyping/inductiveops.cmi \
    kernel/inductive.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/csymtable.cmi \
    config/coq_config.cmi kernel/context.cmi kernel/constr.cmi \
    lib/cErrors.cmi pretyping/vnorm.cmi
pretyping/vnorm.cmx : kernel/vmvalues.cmx kernel/vm.cmx kernel/vconv.cmx \
    kernel/vars.cmx lib/util.cmx kernel/univ.cmx kernel/typeops.cmx \
    engine/termops.cmx kernel/term.cmx kernel/retroknowledge.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx lib/pp.cmx \
    kernel/names.cmx clib/int.cmx pretyping/inductiveops.cmx \
    kernel/inductive.cmx engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/csymtable.cmx \
    config/coq_config.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cErrors.cmx pretyping/vnorm.cmi
pretyping/vnorm.cmi : engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi
printing/genprint.cmo : lib/pp.cmi parsing/notation_gram.cmo \
    pretyping/geninterp.cmi lib/genarg.cmi engine/evd.cmi kernel/environ.cmi \
    lib/cErrors.cmi printing/genprint.cmi
printing/genprint.cmx : lib/pp.cmx parsing/notation_gram.cmx \
    pretyping/geninterp.cmx lib/genarg.cmx engine/evd.cmx kernel/environ.cmx \
    lib/cErrors.cmx printing/genprint.cmi
printing/genprint.cmi : lib/pp.cmi parsing/notation_gram.cmo \
    pretyping/geninterp.cmi lib/genarg.cmi engine/evd.cmi kernel/environ.cmi
printing/ppconstr.cmo : lib/util.cmi engine/termops.cmi printing/pputils.cmi \
    parsing/ppextend.cmi lib/pp.cmi clib/option.cmi interp/notation_ops.cmi \
    parsing/notation_gram.cmo kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi pretyping/locus.cmo lib/loc.cmi library/libnames.cmi \
    clib/int.cmi library/global.cmi pretyping/glob_term.cmo lib/flags.cmi \
    engine/evd.cmi library/decl_kinds.cmo interp/constrintern.cmi \
    interp/constrextern.cmi interp/constrexpr_ops.cmi interp/constrexpr.cmo \
    kernel/constr.cmi lib/cErrors.cmi lib/cAst.cmi printing/ppconstr.cmi
printing/ppconstr.cmx : lib/util.cmx engine/termops.cmx printing/pputils.cmx \
    parsing/ppextend.cmx lib/pp.cmx clib/option.cmx interp/notation_ops.cmx \
    parsing/notation_gram.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx pretyping/locus.cmx lib/loc.cmx library/libnames.cmx \
    clib/int.cmx library/global.cmx pretyping/glob_term.cmx lib/flags.cmx \
    engine/evd.cmx library/decl_kinds.cmx interp/constrintern.cmx \
    interp/constrextern.cmx interp/constrexpr_ops.cmx interp/constrexpr.cmx \
    kernel/constr.cmx lib/cErrors.cmx lib/cAst.cmx printing/ppconstr.cmi
printing/ppconstr.cmi : lib/pp.cmi pretyping/pattern.cmo \
    parsing/notation_gram.cmo kernel/names.cmi pretyping/locus.cmo \
    lib/loc.cmi library/libnames.cmi pretyping/glob_term.cmo \
    interp/constrexpr.cmo
printing/pputils.cmo : lib/util.cmi lib/pp.cmi kernel/names.cmi \
    pretyping/locus.cmo lib/loc.cmi interp/genredexpr.cmo \
    printing/genprint.cmi lib/genarg.cmi lib/flags.cmi interp/constrexpr.cmo \
    lib/cErrors.cmi lib/cAst.cmi printing/pputils.cmi
printing/pputils.cmx : lib/util.cmx lib/pp.cmx kernel/names.cmx \
    pretyping/locus.cmx lib/loc.cmx interp/genredexpr.cmx \
    printing/genprint.cmx lib/genarg.cmx lib/flags.cmx interp/constrexpr.cmx \
    lib/cErrors.cmx lib/cAst.cmx printing/pputils.cmi
printing/pputils.cmi : lib/pp.cmi pretyping/locus.cmo lib/loc.cmi \
    interp/genredexpr.cmo lib/genarg.cmi engine/evd.cmi kernel/environ.cmi \
    interp/constrexpr.cmo lib/cAst.cmi
printing/prettyp.cmo : kernel/vars.cmi lib/util.cmi engine/univNames.cmi \
    kernel/univ.cmi engine/uState.cmi pretyping/typeclasses.cmi \
    engine/termops.cmi kernel/term.cmi interp/syntax_def.cmi \
    interp/smartlocate.cmi kernel/safe_typing.cmi pretyping/reductionops.cmi \
    pretyping/recordops.cmi printing/printmod.cmi printing/printer.cmi \
    lib/pp.cmi clib/option.cmi kernel/opaqueproof.cmi \
    interp/notation_term.cmo interp/notation_ops.cmi interp/notation.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    kernel/mod_subst.cmi library/libobject.cmi library/libnames.cmi \
    library/lib.cmi clib/int.cmi interp/impargs.cmi library/globnames.cmi \
    library/global.cmi lib/flags.cmi engine/evd.cmi kernel/environ.cmi \
    kernel/entries.cmo engine/eConstr.cmi interp/dumpglob.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/conv_oracle.cmi \
    kernel/context.cmi interp/constrextern.cmi interp/constrexpr.cmo \
    kernel/constr.cmi pretyping/classops.cmi lib/cErrors.cmi lib/cAst.cmi \
    pretyping/arguments_renaming.cmi printing/prettyp.cmi
printing/prettyp.cmx : kernel/vars.cmx lib/util.cmx engine/univNames.cmx \
    kernel/univ.cmx engine/uState.cmx pretyping/typeclasses.cmx \
    engine/termops.cmx kernel/term.cmx interp/syntax_def.cmx \
    interp/smartlocate.cmx kernel/safe_typing.cmx pretyping/reductionops.cmx \
    pretyping/recordops.cmx printing/printmod.cmx printing/printer.cmx \
    lib/pp.cmx clib/option.cmx kernel/opaqueproof.cmx \
    interp/notation_term.cmx interp/notation_ops.cmx interp/notation.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    kernel/mod_subst.cmx library/libobject.cmx library/libnames.cmx \
    library/lib.cmx clib/int.cmx interp/impargs.cmx library/globnames.cmx \
    library/global.cmx lib/flags.cmx engine/evd.cmx kernel/environ.cmx \
    kernel/entries.cmx engine/eConstr.cmx interp/dumpglob.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/conv_oracle.cmx \
    kernel/context.cmx interp/constrextern.cmx interp/constrexpr.cmx \
    kernel/constr.cmx pretyping/classops.cmx lib/cErrors.cmx lib/cAst.cmx \
    pretyping/arguments_renaming.cmx printing/prettyp.cmi
printing/prettyp.cmi : engine/univNames.cmi engine/termops.cmi \
    kernel/safe_typing.cmi pretyping/reductionops.cmi lib/pp.cmi \
    kernel/names.cmi library/libnames.cmi library/lib.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi interp/constrexpr.cmo \
    kernel/constr.cmi pretyping/classops.cmi
printing/printer.cmo : lib/util.cmi kernel/univ.cmi engine/termops.cmi \
    pretyping/tacred.cmi pretyping/retyping.cmi proofs/refiner.cmi \
    proofs/refine.cmi kernel/reduction.cmi proofs/proof_type.cmo \
    printing/proof_diffs.cmi proofs/proof_bullet.cmi proofs/proof.cmi \
    printing/ppconstr.cmi lib/pp_diff.cmi lib/pp.cmi proofs/pfedit.cmi \
    clib/option.cmi library/nametab.cmi kernel/names.cmi engine/namegen.cmi \
    library/libnames.cmi clib/int.cmi lib/hook.cmi library/goptions.cmi \
    proofs/goal.cmi library/globnames.cmi library/global.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi kernel/evar.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    pretyping/detyping.cmi kernel/declarations.cmo kernel/context.cmi \
    interp/constrextern.cmi kernel/constr.cmi clib/cList.cmi lib/cErrors.cmi \
    printing/printer.cmi
printing/printer.cmx : lib/util.cmx kernel/univ.cmx engine/termops.cmx \
    pretyping/tacred.cmx pretyping/retyping.cmx proofs/refiner.cmx \
    proofs/refine.cmx kernel/reduction.cmx proofs/proof_type.cmx \
    printing/proof_diffs.cmx proofs/proof_bullet.cmx proofs/proof.cmx \
    printing/ppconstr.cmx lib/pp_diff.cmx lib/pp.cmx proofs/pfedit.cmx \
    clib/option.cmx library/nametab.cmx kernel/names.cmx engine/namegen.cmx \
    library/libnames.cmx clib/int.cmx lib/hook.cmx library/goptions.cmx \
    proofs/goal.cmx library/globnames.cmx library/global.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx kernel/evar.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    pretyping/detyping.cmx kernel/declarations.cmx kernel/context.cmx \
    interp/constrextern.cmx kernel/constr.cmx clib/cList.cmx lib/cErrors.cmx \
    printing/printer.cmi
printing/printer.cmi : kernel/univ.cmi kernel/sorts.cmi \
    proofs/proof_type.cmo proofs/proof.cmi lib/pp.cmi pretyping/pattern.cmo \
    parsing/notation_gram.cmo kernel/names.cmi pretyping/ltac_pretype.cmo \
    pretyping/glob_term.cmo engine/evd.cmi kernel/evar.cmi kernel/environ.cmi \
    kernel/entries.cmo engine/eConstr.cmi kernel/constr.cmi clib/cMap.cmi
printing/printmod.cmo : kernel/vars.cmi lib/util.cmi engine/univNames.cmi \
    kernel/univ.cmi engine/uState.cmi library/states.cmi kernel/reduction.cmi \
    printing/printer.cmi lib/pp.cmi clib/option.cmi library/nametab.cmi \
    kernel/names.cmi engine/namegen.cmi kernel/modops.cmi \
    kernel/mod_subst.cmi library/libnames.cmi kernel/inductive.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    lib/flags.cmi engine/evd.cmi kernel/environ.cmi kernel/declareops.cmi \
    library/declaremods.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi printing/printmod.cmi
printing/printmod.cmx : kernel/vars.cmx lib/util.cmx engine/univNames.cmx \
    kernel/univ.cmx engine/uState.cmx library/states.cmx kernel/reduction.cmx \
    printing/printer.cmx lib/pp.cmx clib/option.cmx library/nametab.cmx \
    kernel/names.cmx engine/namegen.cmx kernel/modops.cmx \
    kernel/mod_subst.cmx library/libnames.cmx kernel/inductive.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    lib/flags.cmx engine/evd.cmx kernel/environ.cmx kernel/declareops.cmx \
    library/declaremods.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx printing/printmod.cmi
printing/printmod.cmi : engine/univNames.cmi lib/pp.cmi kernel/names.cmi \
    kernel/environ.cmi kernel/declarations.cmo
printing/proof_diffs.cmo : parsing/tok.cmi engine/termops.cmi \
    proofs/refiner.cmi proofs/proof.cmi printing/ppconstr.cmi lib/pp_diff.cmi \
    lib/pp.cmi proofs/pfedit.cmi kernel/names.cmi library/goptions.cmi \
    proofs/goal.cmi pretyping/glob_term.cmo engine/evd.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    interp/constrextern.cmi interp/constrexpr.cmo kernel/constr.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi printing/proof_diffs.cmi
printing/proof_diffs.cmx : parsing/tok.cmx engine/termops.cmx \
    proofs/refiner.cmx proofs/proof.cmx printing/ppconstr.cmx lib/pp_diff.cmx \
    lib/pp.cmx proofs/pfedit.cmx kernel/names.cmx library/goptions.cmx \
    proofs/goal.cmx pretyping/glob_term.cmx engine/evd.cmx kernel/evar.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    interp/constrextern.cmx interp/constrexpr.cmx kernel/constr.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx printing/proof_diffs.cmi
printing/proof_diffs.cmi : proofs/proof_type.cmo proofs/proof.cmi lib/pp.cmi \
    proofs/goal.cmi engine/evd.cmi kernel/evar.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi
proofs/clenv.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    pretyping/unification.cmi pretyping/typing.cmi pretyping/typeclasses.cmi \
    engine/termops.cmi proofs/tactypes.cmo pretyping/tacred.cmi \
    proofs/tacmach.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    kernel/reduction.cmi engine/proofview.cmi pretyping/pretype_errors.cmi \
    lib/pp.cmi clib/option.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi clib/int.cmi proofs/goal.cmi engine/evd.cmi \
    engine/evarutil.cmi engine/evar_kinds.cmi kernel/environ.cmi \
    engine/eConstr.cmi kernel/constr.cmi pretyping/coercion.cmi \
    lib/cErrors.cmi lib/cAst.cmi proofs/clenv.cmi
proofs/clenv.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    pretyping/unification.cmx pretyping/typing.cmx pretyping/typeclasses.cmx \
    engine/termops.cmx proofs/tactypes.cmx pretyping/tacred.cmx \
    proofs/tacmach.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    kernel/reduction.cmx engine/proofview.cmx pretyping/pretype_errors.cmx \
    lib/pp.cmx clib/option.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx clib/int.cmx proofs/goal.cmx engine/evd.cmx \
    engine/evarutil.cmx engine/evar_kinds.cmx kernel/environ.cmx \
    engine/eConstr.cmx kernel/constr.cmx pretyping/coercion.cmx \
    lib/cErrors.cmx lib/cAst.cmx proofs/clenv.cmi
proofs/clenv.cmi : kernel/univ.cmi pretyping/unification.cmi \
    proofs/tactypes.cmo engine/proofview.cmi lib/pp.cmi kernel/names.cmi \
    proofs/goal.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/constr.cmi
proofs/clenvtac.cmo : lib/util.cmi pretyping/unification.cmi \
    pretyping/typing.cmi pretyping/typeclasses.cmi engine/termops.cmi \
    proofs/tacmach.cmi proofs/refiner.cmi kernel/reduction.cmi \
    engine/proofview.cmi kernel/names.cmi proofs/logic.cmi engine/evd.cmi \
    kernel/evar.cmi engine/eConstr.cmi kernel/constr.cmi proofs/clenv.cmi \
    lib/cErrors.cmi proofs/clenvtac.cmi
proofs/clenvtac.cmx : lib/util.cmx pretyping/unification.cmx \
    pretyping/typing.cmx pretyping/typeclasses.cmx engine/termops.cmx \
    proofs/tacmach.cmx proofs/refiner.cmx kernel/reduction.cmx \
    engine/proofview.cmx kernel/names.cmx proofs/logic.cmx engine/evd.cmx \
    kernel/evar.cmx engine/eConstr.cmx kernel/constr.cmx proofs/clenv.cmx \
    lib/cErrors.cmx proofs/clenvtac.cmi
proofs/clenvtac.cmi : pretyping/unification.cmi engine/proofview.cmi \
    engine/eConstr.cmi proofs/clenv.cmi
proofs/evar_refiner.cmo : lib/util.cmi engine/termops.cmi \
    pretyping/pretyping.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    kernel/names.cmi pretyping/ltac_pretype.cmo pretyping/glob_term.cmo \
    pretyping/glob_ops.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarsolve.cmi pretyping/evarconv.cmi kernel/evar.cmi \
    lib/cErrors.cmi proofs/evar_refiner.cmi
proofs/evar_refiner.cmx : lib/util.cmx engine/termops.cmx \
    pretyping/pretyping.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    kernel/names.cmx pretyping/ltac_pretype.cmx pretyping/glob_term.cmx \
    pretyping/glob_ops.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarsolve.cmx pretyping/evarconv.cmx kernel/evar.cmx \
    lib/cErrors.cmx proofs/evar_refiner.cmi
proofs/evar_refiner.cmi : pretyping/ltac_pretype.cmo pretyping/glob_term.cmo \
    engine/evd.cmi kernel/evar.cmi
proofs/goal.cmo : lib/util.cmi pretyping/typeclasses.cmi engine/termops.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi lib/loc.cmi library/global.cmi \
    engine/evd.cmi engine/evarutil.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    kernel/constr.cmi proofs/goal.cmi
proofs/goal.cmx : lib/util.cmx pretyping/typeclasses.cmx engine/termops.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx lib/loc.cmx library/global.cmx \
    engine/evd.cmx engine/evarutil.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    kernel/constr.cmx proofs/goal.cmi
proofs/goal.cmi : lib/pp.cmi engine/evd.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi
proofs/goal_select.cmo : lib/pp.cmi kernel/names.cmi library/goptions.cmi \
    lib/cErrors.cmi proofs/goal_select.cmi
proofs/goal_select.cmx : lib/pp.cmx kernel/names.cmx library/goptions.cmx \
    lib/cErrors.cmx proofs/goal_select.cmi
proofs/goal_select.cmi : lib/pp.cmi kernel/names.cmi
proofs/logic.cmo : kernel/vars.cmi lib/util.cmi pretyping/typing.cmi \
    kernel/type_errors.cmi engine/termops.cmi kernel/term.cmi \
    pretyping/tacred.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    proofs/proof_type.cmo pretyping/pretype_errors.cmi lib/pp.cmi \
    clib/option.cmi interp/notation.cmi library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi clib/int.cmi pretyping/inductiveops.cmi \
    pretyping/indrec.cmi proofs/goal.cmi library/global.cmi lib/flags.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi clib/cArray.cmi proofs/logic.cmi
proofs/logic.cmx : kernel/vars.cmx lib/util.cmx pretyping/typing.cmx \
    kernel/type_errors.cmx engine/termops.cmx kernel/term.cmx \
    pretyping/tacred.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    proofs/proof_type.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    clib/option.cmx interp/notation.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx clib/int.cmx pretyping/inductiveops.cmx \
    pretyping/indrec.cmx proofs/goal.cmx library/global.cmx lib/flags.cmx \
    engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx clib/cArray.cmx proofs/logic.cmi
proofs/logic.cmi : proofs/proof_type.cmo lib/pp.cmi kernel/names.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi
proofs/miscprint.cmo : proofs/tactypes.cmo lib/pp.cmi kernel/names.cmi \
    engine/namegen.cmi lib/cAst.cmi proofs/miscprint.cmi
proofs/miscprint.cmx : proofs/tactypes.cmx lib/pp.cmx kernel/names.cmx \
    engine/namegen.cmx lib/cAst.cmx proofs/miscprint.cmi
proofs/miscprint.cmi : proofs/tactypes.cmo lib/pp.cmi engine/namegen.cmi \
    lib/cAst.cmi
proofs/pfedit.cmo : lib/util.cmi engine/uState.cmi library/summary.cmi \
    kernel/safe_typing.cmi proofs/refiner.cmi proofs/refine.cmi \
    engine/proofview.cmi proofs/proof_global.cmi proofs/proof.cmi lib/pp.cmi \
    kernel/names.cmi engine/logic_monad.cmi proofs/logic.cmi \
    library/goptions.cmi proofs/goal_select.cmi library/global.cmi \
    lib/future.cmi lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi \
    engine/evar_kinds.cmi kernel/environ.cmi kernel/entries.cmo \
    engine/eConstr.cmi library/decl_kinds.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi proofs/pfedit.cmi
proofs/pfedit.cmx : lib/util.cmx engine/uState.cmx library/summary.cmx \
    kernel/safe_typing.cmx proofs/refiner.cmx proofs/refine.cmx \
    engine/proofview.cmx proofs/proof_global.cmx proofs/proof.cmx lib/pp.cmx \
    kernel/names.cmx engine/logic_monad.cmx proofs/logic.cmx \
    library/goptions.cmx proofs/goal_select.cmx library/global.cmx \
    lib/future.cmx lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx \
    engine/evar_kinds.cmx kernel/environ.cmx kernel/entries.cmx \
    engine/eConstr.cmx library/decl_kinds.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx proofs/pfedit.cmi
proofs/pfedit.cmi : engine/uState.cmi kernel/safe_typing.cmi \
    engine/proofview.cmi proofs/proof_global.cmi proofs/proof.cmi \
    pretyping/pretyping.cmi kernel/names.cmi proofs/goal_select.cmi \
    engine/evd.cmi kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    library/decl_kinds.cmo interp/constrexpr.cmo kernel/constr.cmi
proofs/proof.cmo : lib/util.cmi engine/uState.cmi engine/proofview.cmi \
    lib/pp.cmi kernel/names.cmi clib/int.cmi proofs/goal.cmi \
    library/global.cmi pretyping/glob_ops.cmi engine/evd.cmi \
    engine/evarutil.cmi proofs/evar_refiner.cmi kernel/evar.cmi \
    interp/constrintern.cmi clib/cList.cmi lib/cErrors.cmi proofs/proof.cmi
proofs/proof.cmx : lib/util.cmx engine/uState.cmx engine/proofview.cmx \
    lib/pp.cmx kernel/names.cmx clib/int.cmx proofs/goal.cmx \
    library/global.cmx pretyping/glob_ops.cmx engine/evd.cmx \
    engine/evarutil.cmx proofs/evar_refiner.cmx kernel/evar.cmx \
    interp/constrintern.cmx clib/cList.cmx lib/cErrors.cmx proofs/proof.cmi
proofs/proof.cmi : engine/uState.cmi engine/proofview_monad.cmi \
    engine/proofview.cmi lib/pp.cmi kernel/names.cmi proofs/goal.cmi \
    engine/evd.cmi kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi \
    interp/constrexpr.cmo
proofs/proof_bullet.cmo : proofs/proof.cmi lib/pp.cmi library/goptions.cmi \
    proofs/goal_select.cmi lib/cErrors.cmi proofs/proof_bullet.cmi
proofs/proof_bullet.cmx : proofs/proof.cmx lib/pp.cmx library/goptions.cmx \
    proofs/goal_select.cmx lib/cErrors.cmx proofs/proof_bullet.cmi
proofs/proof_bullet.cmi : proofs/proof.cmi lib/pp.cmi proofs/goal_select.cmi
proofs/proof_global.cmo : lib/util.cmi engine/univops.cmi \
    engine/univSubst.cmi kernel/univ.cmi engine/uState.cmi \
    kernel/safe_typing.cmi engine/proofview.cmi proofs/proof_bullet.cmi \
    proofs/proof.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi clib/int.cmi \
    library/goptions.cmi library/global.cmi pretyping/geninterp.cmi \
    lib/genarg.cmi lib/future.cmi engine/ftactic.cmi engine/evd.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    library/decl_kinds.cmo kernel/context.cmi kernel/constr.cmi \
    lib/cErrors.cmi clib/cEphemeron.cmi lib/cAst.cmi proofs/proof_global.cmi
proofs/proof_global.cmx : lib/util.cmx engine/univops.cmx \
    engine/univSubst.cmx kernel/univ.cmx engine/uState.cmx \
    kernel/safe_typing.cmx engine/proofview.cmx proofs/proof_bullet.cmx \
    proofs/proof.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx clib/int.cmx \
    library/goptions.cmx library/global.cmx pretyping/geninterp.cmx \
    lib/genarg.cmx lib/future.cmx engine/ftactic.cmx engine/evd.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    library/decl_kinds.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cErrors.cmx clib/cEphemeron.cmx lib/cAst.cmx proofs/proof_global.cmi
proofs/proof_global.cmi : engine/uState.cmi lib/stateid.cmi \
    kernel/safe_typing.cmi engine/proofview.cmi proofs/proof.cmi \
    kernel/names.cmi lib/genarg.cmi lib/future.cmi engine/evd.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    library/decl_kinds.cmo kernel/constr.cmi
proofs/proof_type.cmo : proofs/goal.cmi engine/evd.cmi kernel/constr.cmi
proofs/proof_type.cmx : proofs/goal.cmx engine/evd.cmx kernel/constr.cmx
proofs/redexpr.cmo : pretyping/vnorm.cmi lib/util.cmi pretyping/tacred.cmi \
    library/summary.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    interp/redops.cmi lib/pp.cmi pretyping/patternops.cmi \
    pretyping/pattern.cmo pretyping/nativenorm.cmi library/nametab.cmi \
    kernel/names.cmi kernel/mod_subst.cmi pretyping/locusops.cmi \
    pretyping/locus.cmo library/libobject.cmi library/lib.cmi \
    library/goptions.cmi library/globnames.cmi library/global.cmi \
    interp/genredexpr.cmo kernel/environ.cmi engine/eConstr.cmi \
    kernel/declarations.cmo kernel/csymtable.cmi config/coq_config.cmi \
    kernel/conv_oracle.cmi kernel/constr.cmi lib/cWarnings.cmi \
    lib/cErrors.cmi kernel/cClosure.cmi proofs/redexpr.cmi
proofs/redexpr.cmx : pretyping/vnorm.cmx lib/util.cmx pretyping/tacred.cmx \
    library/summary.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    interp/redops.cmx lib/pp.cmx pretyping/patternops.cmx \
    pretyping/pattern.cmx pretyping/nativenorm.cmx library/nametab.cmx \
    kernel/names.cmx kernel/mod_subst.cmx pretyping/locusops.cmx \
    pretyping/locus.cmx library/libobject.cmx library/lib.cmx \
    library/goptions.cmx library/globnames.cmx library/global.cmx \
    interp/genredexpr.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declarations.cmx kernel/csymtable.cmx config/coq_config.cmx \
    kernel/conv_oracle.cmx kernel/constr.cmx lib/cWarnings.cmx \
    lib/cErrors.cmx kernel/cClosure.cmx proofs/redexpr.cmi
proofs/redexpr.cmi : pretyping/reductionops.cmi pretyping/pattern.cmo \
    kernel/names.cmi pretyping/locus.cmo interp/genredexpr.cmo \
    kernel/environ.cmi engine/eConstr.cmi kernel/conv_oracle.cmi \
    kernel/constr.cmi
proofs/refine.cmo : lib/util.cmi pretyping/typing.cmi kernel/safe_typing.cmi \
    pretyping/retyping.cmi engine/proofview.cmi pretyping/pretype_errors.cmi \
    lib/pp.cmi lib/hook.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarconv.cmi kernel/environ.cmi kernel/entries.cmo \
    engine/eConstr.cmi kernel/context.cmi pretyping/coercion.cmi \
    clib/cList.cmi proofs/refine.cmi
proofs/refine.cmx : lib/util.cmx pretyping/typing.cmx kernel/safe_typing.cmx \
    pretyping/retyping.cmx engine/proofview.cmx pretyping/pretype_errors.cmx \
    lib/pp.cmx lib/hook.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarconv.cmx kernel/environ.cmx kernel/entries.cmx \
    engine/eConstr.cmx kernel/context.cmx pretyping/coercion.cmx \
    clib/cList.cmx proofs/refine.cmi
proofs/refine.cmi : engine/proofview.cmi lib/pp.cmi lib/hook.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi
proofs/refiner.cmo : lib/util.cmi proofs/proof_type.cmo lib/pp.cmi \
    kernel/names.cmi proofs/logic.cmi clib/int.cmi proofs/goal.cmi \
    library/global.cmi lib/flags.cmi lib/feedback.cmi engine/evd.cmi \
    engine/eConstr.cmi lib/control.cmi kernel/context.cmi lib/cProfile.cmi \
    lib/cErrors.cmi proofs/refiner.cmi
proofs/refiner.cmx : lib/util.cmx proofs/proof_type.cmx lib/pp.cmx \
    kernel/names.cmx proofs/logic.cmx clib/int.cmx proofs/goal.cmx \
    library/global.cmx lib/flags.cmx lib/feedback.cmx engine/evd.cmx \
    engine/eConstr.cmx lib/control.cmx kernel/context.cmx lib/cProfile.cmx \
    lib/cErrors.cmx proofs/refiner.cmi
proofs/refiner.cmi : kernel/univ.cmi engine/uState.cmi proofs/proof_type.cmo \
    lib/pp.cmi clib/exninfo.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi
proofs/tacmach.cmo : lib/util.cmi engine/univGen.cmi pretyping/typing.cmi \
    engine/termops.cmi pretyping/tacred.cmi pretyping/retyping.cmi \
    proofs/refiner.cmi pretyping/reductionops.cmi kernel/reduction.cmi \
    proofs/redexpr.cmi engine/proofview.cmi proofs/proof_type.cmo lib/pp.cmi \
    engine/namegen.cmi proofs/logic.cmi proofs/goal.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    interp/constrintern.cmi proofs/tacmach.cmi
proofs/tacmach.cmx : lib/util.cmx engine/univGen.cmx pretyping/typing.cmx \
    engine/termops.cmx pretyping/tacred.cmx pretyping/retyping.cmx \
    proofs/refiner.cmx pretyping/reductionops.cmx kernel/reduction.cmx \
    proofs/redexpr.cmx engine/proofview.cmx proofs/proof_type.cmx lib/pp.cmx \
    engine/namegen.cmx proofs/logic.cmx proofs/goal.cmx engine/evd.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    interp/constrintern.cmx proofs/tacmach.cmi
proofs/tacmach.cmi : proofs/redexpr.cmi engine/proofview.cmi \
    proofs/proof_type.cmo lib/pp.cmi kernel/names.cmi pretyping/locus.cmo \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi kernel/constr.cmi
proofs/tactypes.cmo : kernel/names.cmi engine/namegen.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi lib/cAst.cmi
proofs/tactypes.cmx : kernel/names.cmx engine/namegen.cmx engine/evd.cmx \
    kernel/environ.cmx engine/eConstr.cmx lib/cAst.cmx
stm/asyncTaskQueue.cmo : stm/workerPool.cmi lib/util.cmi engine/univGen.cmi \
    stm/tQueue.cmi lib/system.cmi lib/stateid.cmi stm/spawned.cmi \
    lib/spawn.cmi lib/pp.cmi clib/option.cmi lib/flags.cmi lib/feedback.cmi \
    stm/coqworkmgrApi.cmi clib/cThread.cmi clib/cList.cmi lib/cErrors.cmi \
    clib/cEphemeron.cmi stm/asyncTaskQueue.cmi
stm/asyncTaskQueue.cmx : stm/workerPool.cmx lib/util.cmx engine/univGen.cmx \
    stm/tQueue.cmx lib/system.cmx lib/stateid.cmx stm/spawned.cmx \
    lib/spawn.cmx lib/pp.cmx clib/option.cmx lib/flags.cmx lib/feedback.cmx \
    stm/coqworkmgrApi.cmx clib/cThread.cmx clib/cList.cmx lib/cErrors.cmx \
    clib/cEphemeron.cmx stm/asyncTaskQueue.cmi
stm/asyncTaskQueue.cmi : stm/workerPool.cmi lib/feedback.cmi
stm/coqworkmgrApi.cmo : stm/coqworkmgrApi.cmi
stm/coqworkmgrApi.cmx : stm/coqworkmgrApi.cmi
stm/coqworkmgrApi.cmi :
stm/dag.cmo : clib/int.cmi clib/cMap.cmi stm/dag.cmi
stm/dag.cmx : clib/int.cmx clib/cMap.cmx stm/dag.cmi
stm/dag.cmi :
stm/proofBlockDelimiter.cmo : vernac/vernacstate.cmi vernac/vernacprop.cmi \
    vernac/vernacexpr.cmo stm/stm.cmi lib/stateid.cmi engine/proofview.cmi \
    proofs/proof_global.cmi proofs/proof_bullet.cmi proofs/proof.cmi \
    proofs/goal.cmi engine/evd.cmi engine/evarutil.cmi kernel/evar.cmi \
    engine/eConstr.cmi stm/proofBlockDelimiter.cmi
stm/proofBlockDelimiter.cmx : vernac/vernacstate.cmx vernac/vernacprop.cmx \
    vernac/vernacexpr.cmx stm/stm.cmx lib/stateid.cmx engine/proofview.cmx \
    proofs/proof_global.cmx proofs/proof_bullet.cmx proofs/proof.cmx \
    proofs/goal.cmx engine/evd.cmx engine/evarutil.cmx kernel/evar.cmx \
    engine/eConstr.cmx stm/proofBlockDelimiter.cmi
stm/proofBlockDelimiter.cmi : stm/stm.cmi lib/stateid.cmi \
    proofs/proof_bullet.cmi proofs/goal.cmi engine/evd.cmi
stm/spawned.cmo : lib/spawn.cmi lib/pp.cmi lib/flags.cmi clib/cThread.cmi \
    lib/cErrors.cmi stm/spawned.cmi
stm/spawned.cmx : lib/spawn.cmx lib/pp.cmx lib/flags.cmx clib/cThread.cmx \
    lib/cErrors.cmx stm/spawned.cmi
stm/spawned.cmi : clib/cThread.cmi
stm/stm.cmo : stm/workerPool.cmi vernac/vernacstate.cmi \
    vernac/vernacprop.cmi vernac/vernacexpr.cmo vernac/vernacentries.cmi \
    stm/vernac_classifier.cmi stm/vcs.cmi lib/util.cmi kernel/univ.cmi \
    engine/uState.cmi engine/termops.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi lib/system.cmi library/summary.cmi \
    library/states.cmi lib/stateid.cmi stm/spawned.cmi kernel/safe_typing.cmi \
    lib/remoteCounter.cmi proofs/refiner.cmi vernac/pvernac.cmi \
    engine/proofview.cmi proofs/proof_global.cmi proofs/proof.cmi \
    printing/printer.cmi vernac/ppvernac.cmi lib/pp.cmi proofs/pfedit.cmi \
    parsing/pcoq.cmi clib/option.cmi kernel/opaqueproof.cmi \
    vernac/obligations.cmi library/nametab.cmi kernel/names.cmi \
    vernac/mltop.cmi lib/loc.cmi library/library.cmi library/libnames.cmi \
    library/lib.cmi vernac/lemmas.cmi clib/int.cmi lib/hook.cmi \
    library/goptions.cmi proofs/goal_select.cmi proofs/goal.cmi \
    library/global.cmi lib/future.cmi lib/flags.cmi lib/feedback.cmi \
    vernac/explainErr.cmi clib/exninfo.cmi engine/evd.cmi engine/evarutil.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi clib/dyn.cmi \
    library/declaremods.cmi kernel/declarations.cmo stm/dag.cmi \
    kernel/cooking.cmi lib/control.cmi kernel/context.cmi kernel/constr.cmi \
    lib/cWarnings.cmi clib/cList.cmi lib/cErrors.cmi lib/cAst.cmi \
    lib/aux_file.cmi stm/asyncTaskQueue.cmi stm/stm.cmi
stm/stm.cmx : stm/workerPool.cmx vernac/vernacstate.cmx \
    vernac/vernacprop.cmx vernac/vernacexpr.cmx vernac/vernacentries.cmx \
    stm/vernac_classifier.cmx stm/vcs.cmx lib/util.cmx kernel/univ.cmx \
    engine/uState.cmx engine/termops.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx lib/system.cmx library/summary.cmx \
    library/states.cmx lib/stateid.cmx stm/spawned.cmx kernel/safe_typing.cmx \
    lib/remoteCounter.cmx proofs/refiner.cmx vernac/pvernac.cmx \
    engine/proofview.cmx proofs/proof_global.cmx proofs/proof.cmx \
    printing/printer.cmx vernac/ppvernac.cmx lib/pp.cmx proofs/pfedit.cmx \
    parsing/pcoq.cmx clib/option.cmx kernel/opaqueproof.cmx \
    vernac/obligations.cmx library/nametab.cmx kernel/names.cmx \
    vernac/mltop.cmx lib/loc.cmx library/library.cmx library/libnames.cmx \
    library/lib.cmx vernac/lemmas.cmx clib/int.cmx lib/hook.cmx \
    library/goptions.cmx proofs/goal_select.cmx proofs/goal.cmx \
    library/global.cmx lib/future.cmx lib/flags.cmx lib/feedback.cmx \
    vernac/explainErr.cmx clib/exninfo.cmx engine/evd.cmx engine/evarutil.cmx \
    kernel/evar.cmx kernel/environ.cmx engine/eConstr.cmx clib/dyn.cmx \
    library/declaremods.cmx kernel/declarations.cmx stm/dag.cmx \
    kernel/cooking.cmx lib/control.cmx kernel/context.cmx kernel/constr.cmx \
    lib/cWarnings.cmx clib/cList.cmx lib/cErrors.cmx lib/cAst.cmx \
    lib/aux_file.cmx stm/asyncTaskQueue.cmx stm/stm.cmi
stm/stm.cmi : vernac/vernacstate.cmi vernac/vernacexpr.cmo lib/stateid.cmi \
    proofs/proof.cmi parsing/pcoq.cmi kernel/names.cmi vernac/mltop.cmi \
    lib/loc.cmi library/library.cmi lib/hook.cmi proofs/goal.cmi \
    lib/feedback.cmi clib/exninfo.cmi clib/dyn.cmi lib/cAst.cmi \
    stm/asyncTaskQueue.cmi
stm/tQueue.cmo : lib/pp.cmi lib/cErrors.cmi stm/tQueue.cmi
stm/tQueue.cmx : lib/pp.cmx lib/cErrors.cmx stm/tQueue.cmi
stm/tQueue.cmi :
stm/vcs.cmo : lib/pp.cmi stm/dag.cmi clib/cString.cmi clib/cList.cmi \
    lib/cErrors.cmi stm/vcs.cmi
stm/vcs.cmx : lib/pp.cmx stm/dag.cmx clib/cString.cmx clib/cList.cmx \
    lib/cErrors.cmx stm/vcs.cmi
stm/vcs.cmi : stm/dag.cmi
stm/vernac_classifier.cmo : vernac/vernacinterp.cmi vernac/vernacexpr.cmo \
    vernac/vernacentries.cmi lib/util.cmi proofs/proof_global.cmi lib/pp.cmi \
    clib/option.cmi kernel/names.cmi lib/flags.cmi library/decl_kinds.cmo \
    clib/cList.cmi lib/cErrors.cmi lib/cAst.cmi stm/vernac_classifier.cmi
stm/vernac_classifier.cmx : vernac/vernacinterp.cmx vernac/vernacexpr.cmx \
    vernac/vernacentries.cmx lib/util.cmx proofs/proof_global.cmx lib/pp.cmx \
    clib/option.cmx kernel/names.cmx lib/flags.cmx library/decl_kinds.cmx \
    clib/cList.cmx lib/cErrors.cmx lib/cAst.cmx stm/vernac_classifier.cmi
stm/vernac_classifier.cmi : vernac/vernacexpr.cmo
stm/vio_checking.cmo : lib/util.cmi stm/stm.cmi lib/spawn.cmi lib/pp.cmi \
    library/loadpath.cmi library/library.cmi interp/dumpglob.cmi \
    lib/cErrors.cmi lib/aux_file.cmi stm/vio_checking.cmi
stm/vio_checking.cmx : lib/util.cmx stm/stm.cmx lib/spawn.cmx lib/pp.cmx \
    library/loadpath.cmx library/library.cmx interp/dumpglob.cmx \
    lib/cErrors.cmx lib/aux_file.cmx stm/vio_checking.cmi
stm/vio_checking.cmi :
stm/workerPool.cmo : clib/cThread.cmi clib/cList.cmi lib/cErrors.cmi \
    stm/workerPool.cmi
stm/workerPool.cmx : clib/cThread.cmx clib/cList.cmx lib/cErrors.cmx \
    stm/workerPool.cmi
stm/workerPool.cmi : clib/cThread.cmi
tactics/auto.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    pretyping/unification.cmi engine/termops.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi proofs/tacmach.cmi interp/stdarg.cmi \
    engine/proofview.cmi lib/pp.cmi proofs/pfedit.cmi clib/option.cmi \
    kernel/names.cmi pretyping/locusops.cmi pretyping/locus.cmo clib/int.cmi \
    tactics/hints.cmi library/goptions.cmi interp/genredexpr.cmo \
    pretyping/geninterp.cmi lib/genarg.cmi engine/ftactic.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi kernel/evar.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/context.cmi \
    pretyping/constr_matching.cmi proofs/clenvtac.cmi proofs/clenv.cmi \
    lib/cProfile.cmi lib/cErrors.cmi tactics/auto.cmi
tactics/auto.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    pretyping/unification.cmx engine/termops.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx proofs/tacmach.cmx interp/stdarg.cmx \
    engine/proofview.cmx lib/pp.cmx proofs/pfedit.cmx clib/option.cmx \
    kernel/names.cmx pretyping/locusops.cmx pretyping/locus.cmx clib/int.cmx \
    tactics/hints.cmx library/goptions.cmx interp/genredexpr.cmx \
    pretyping/geninterp.cmx lib/genarg.cmx engine/ftactic.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx kernel/evar.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/context.cmx \
    pretyping/constr_matching.cmx proofs/clenvtac.cmx proofs/clenv.cmx \
    lib/cProfile.cmx lib/cErrors.cmx tactics/auto.cmi
tactics/auto.cmi : pretyping/unification.cmi proofs/tactypes.cmo \
    engine/proofview.cmi pretyping/pattern.cmo kernel/names.cmi \
    tactics/hints.cmi lib/genarg.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo proofs/clenv.cmi
tactics/autorewrite.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi pretyping/typing.cmi engine/termops.cmi \
    tactics/term_dnet.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    library/summary.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    printing/printer.cmi printing/pputils.cmi lib/pp.cmi clib/option.cmi \
    kernel/names.cmi kernel/mod_subst.cmi pretyping/locus.cmo \
    library/libobject.cmi library/lib.cmi library/global.cmi \
    pretyping/geninterp.cmi interp/genintern.cmi lib/genarg.cmi \
    engine/ftactic.cmi engine/evd.cmi tactics/equality.cmi engine/eConstr.cmi \
    kernel/constr.cmi proofs/clenv.cmi lib/cErrors.cmi lib/cAst.cmi \
    tactics/autorewrite.cmi
tactics/autorewrite.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx pretyping/typing.cmx engine/termops.cmx \
    tactics/term_dnet.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    library/summary.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    printing/printer.cmx printing/pputils.cmx lib/pp.cmx clib/option.cmx \
    kernel/names.cmx kernel/mod_subst.cmx pretyping/locus.cmx \
    library/libobject.cmx library/lib.cmx library/global.cmx \
    pretyping/geninterp.cmx interp/genintern.cmx lib/genarg.cmx \
    engine/ftactic.cmx engine/evd.cmx tactics/equality.cmx engine/eConstr.cmx \
    kernel/constr.cmx proofs/clenv.cmx lib/cErrors.cmx lib/cAst.cmx \
    tactics/autorewrite.cmi
tactics/autorewrite.cmi : kernel/univ.cmi engine/proofview.cmi lib/pp.cmi \
    kernel/names.cmi pretyping/locus.cmo lib/loc.cmi lib/genarg.cmi \
    engine/evd.cmi tactics/equality.cmi kernel/environ.cmi kernel/constr.cmi \
    proofs/clenv.cmi lib/cAst.cmi
tactics/btermdn.cmo : lib/util.cmi pretyping/patternops.cmi \
    pretyping/pattern.cmo kernel/names.cmi clib/int.cmi library/globnames.cmi \
    engine/eConstr.cmi tactics/dn.cmi kernel/constr.cmi tactics/btermdn.cmi
tactics/btermdn.cmx : lib/util.cmx pretyping/patternops.cmx \
    pretyping/pattern.cmx kernel/names.cmx clib/int.cmx library/globnames.cmx \
    engine/eConstr.cmx tactics/dn.cmx kernel/constr.cmx tactics/btermdn.cmi
tactics/btermdn.cmi : pretyping/pattern.cmo kernel/names.cmi engine/evd.cmi \
    engine/eConstr.cmi
tactics/class_tactics.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi clib/unionfind.cmi pretyping/unification.cmi \
    pretyping/typing.cmi pretyping/typeclasses.cmi engine/termops.cmi \
    kernel/term.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi library/summary.cmi clib/store.cmi \
    pretyping/retyping.cmi proofs/refiner.cmi proofs/refine.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi printing/printer.cmi \
    pretyping/pretype_errors.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    engine/logic_monad.cmi proofs/logic.cmi pretyping/locusops.cmi \
    pretyping/locus.cmo library/lib.cmi clib/int.cmi lib/hook.cmi \
    tactics/hints.cmi library/goptions.cmi proofs/goal.cmi \
    library/globnames.cmi library/global.cmi lib/flags.cmi lib/feedback.cmi \
    clib/exninfo.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarconv.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    tactics/eauto.cmi engine/eConstr.cmi kernel/context.cmi \
    pretyping/constr_matching.cmi kernel/constr.cmi proofs/clenvtac.cmi \
    proofs/clenv.cmi clib/cList.cmi lib/cErrors.cmi tactics/auto.cmi \
    tactics/class_tactics.cmi
tactics/class_tactics.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx clib/unionfind.cmx pretyping/unification.cmx \
    pretyping/typing.cmx pretyping/typeclasses.cmx engine/termops.cmx \
    kernel/term.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx library/summary.cmx clib/store.cmx \
    pretyping/retyping.cmx proofs/refiner.cmx proofs/refine.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx printing/printer.cmx \
    pretyping/pretype_errors.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    engine/logic_monad.cmx proofs/logic.cmx pretyping/locusops.cmx \
    pretyping/locus.cmx library/lib.cmx clib/int.cmx lib/hook.cmx \
    tactics/hints.cmx library/goptions.cmx proofs/goal.cmx \
    library/globnames.cmx library/global.cmx lib/flags.cmx lib/feedback.cmx \
    clib/exninfo.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarconv.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    tactics/eauto.cmx engine/eConstr.cmx kernel/context.cmx \
    pretyping/constr_matching.cmx kernel/constr.cmx proofs/clenvtac.cmx \
    proofs/clenv.cmx clib/cList.cmx lib/cErrors.cmx tactics/auto.cmx \
    tactics/class_tactics.cmi
tactics/class_tactics.cmi : engine/proofview.cmi kernel/names.cmi \
    clib/int.cmi tactics/hints.cmi engine/eConstr.cmi
tactics/contradiction.cmo : lib/util.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    pretyping/retyping.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    lib/pp.cmi kernel/names.cmi engine/namegen.cmi pretyping/inductiveops.cmi \
    tactics/hipattern.cmi kernel/environ.cmi engine/eConstr.cmi \
    library/coqlib.cmi kernel/context.cmi kernel/constr.cmi \
    pretyping/coercion.cmi tactics/contradiction.cmi
tactics/contradiction.cmx : lib/util.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    pretyping/retyping.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    lib/pp.cmx kernel/names.cmx engine/namegen.cmx pretyping/inductiveops.cmx \
    tactics/hipattern.cmx kernel/environ.cmx engine/eConstr.cmx \
    library/coqlib.cmx kernel/context.cmx kernel/constr.cmx \
    pretyping/coercion.cmx tactics/contradiction.cmi
tactics/contradiction.cmi : proofs/tactypes.cmo engine/proofview.cmi \
    engine/eConstr.cmi
tactics/dn.cmo : lib/util.cmi clib/trie.cmi clib/int.cmi tactics/dn.cmi
tactics/dn.cmx : lib/util.cmx clib/trie.cmx clib/int.cmx tactics/dn.cmi
tactics/dn.cmi :
tactics/dnet.cmo : clib/option.cmi tactics/dnet.cmi
tactics/dnet.cmx : clib/option.cmx tactics/dnet.cmi
tactics/dnet.cmi :
tactics/eauto.cmo : lib/util.cmi engine/univGen.cmi engine/termops.cmi \
    proofs/tactypes.cmo tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi proofs/refiner.cmi pretyping/reductionops.cmi \
    engine/proofview.cmi proofs/proof_type.cmo lib/pp.cmi kernel/names.cmi \
    pretyping/locusops.cmi pretyping/locus.cmo clib/int.cmi tactics/hints.cmi \
    library/goptions.cmi interp/genredexpr.cmo lib/feedback.cmi \
    lib/explore.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/constr.cmi proofs/clenvtac.cmi proofs/clenv.cmi lib/cErrors.cmi \
    tactics/auto.cmi tactics/eauto.cmi
tactics/eauto.cmx : lib/util.cmx engine/univGen.cmx engine/termops.cmx \
    proofs/tactypes.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx proofs/refiner.cmx pretyping/reductionops.cmx \
    engine/proofview.cmx proofs/proof_type.cmx lib/pp.cmx kernel/names.cmx \
    pretyping/locusops.cmx pretyping/locus.cmx clib/int.cmx tactics/hints.cmx \
    library/goptions.cmx interp/genredexpr.cmx lib/feedback.cmx \
    lib/explore.cmx engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/constr.cmx proofs/clenvtac.cmx proofs/clenv.cmx lib/cErrors.cmx \
    tactics/auto.cmx tactics/eauto.cmi
tactics/eauto.cmi : pretyping/unification.cmi proofs/tactypes.cmo \
    engine/proofview.cmi proofs/proof_type.cmo pretyping/locus.cmo \
    tactics/hints.cmi engine/eConstr.cmi
tactics/elim.cmo : lib/util.cmi kernel/univ.cmi engine/termops.cmi \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    engine/proofview.cmi lib/pp.cmi kernel/names.cmi \
    pretyping/inductiveops.cmi tactics/hipattern.cmi engine/eConstr.cmi \
    kernel/context.cmi tactics/elim.cmi
tactics/elim.cmx : lib/util.cmx kernel/univ.cmx engine/termops.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    engine/proofview.cmx lib/pp.cmx kernel/names.cmx \
    pretyping/inductiveops.cmx tactics/hipattern.cmx engine/eConstr.cmx \
    kernel/context.cmx tactics/elim.cmi
tactics/elim.cmi : proofs/tactypes.cmo tactics/tactics.cmi \
    tactics/tacticals.cmi engine/proofview.cmi kernel/names.cmi \
    engine/eConstr.cmi
tactics/elimschemes.cmo : kernel/typeops.cmi kernel/sorts.cmi \
    kernel/safe_typing.cmi pretyping/inductiveops.cmi pretyping/indrec.cmi \
    tactics/ind_tables.cmi library/global.cmi engine/evd.cmi \
    engine/evarutil.cmi kernel/declarations.cmo kernel/constr.cmi \
    tactics/elimschemes.cmi
tactics/elimschemes.cmx : kernel/typeops.cmx kernel/sorts.cmx \
    kernel/safe_typing.cmx pretyping/inductiveops.cmx pretyping/indrec.cmx \
    tactics/ind_tables.cmx library/global.cmx engine/evd.cmx \
    engine/evarutil.cmx kernel/declarations.cmx kernel/constr.cmx \
    tactics/elimschemes.cmi
tactics/elimschemes.cmi : engine/uState.cmi kernel/sorts.cmi \
    kernel/safe_typing.cmi kernel/names.cmi pretyping/indrec.cmi \
    tactics/ind_tables.cmi kernel/constr.cmi
tactics/eqdecide.cmo : lib/util.cmi engine/termops.cmi proofs/tactypes.cmo \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/tacmach.cmi \
    proofs/refine.cmi engine/proofview.cmi lib/pp.cmi kernel/names.cmi \
    engine/namegen.cmi tactics/hipattern.cmi library/global.cmi \
    engine/evarutil.cmi tactics/equality.cmi engine/eConstr.cmi \
    kernel/declarations.cmo library/coqlib.cmi pretyping/constr_matching.cmi \
    kernel/constr.cmi tactics/auto.cmi tactics/eqdecide.cmi
tactics/eqdecide.cmx : lib/util.cmx engine/termops.cmx proofs/tactypes.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/tacmach.cmx \
    proofs/refine.cmx engine/proofview.cmx lib/pp.cmx kernel/names.cmx \
    engine/namegen.cmx tactics/hipattern.cmx library/global.cmx \
    engine/evarutil.cmx tactics/equality.cmx engine/eConstr.cmx \
    kernel/declarations.cmx library/coqlib.cmx pretyping/constr_matching.cmx \
    kernel/constr.cmx tactics/auto.cmx tactics/eqdecide.cmi
tactics/eqdecide.cmi : engine/proofview.cmi engine/eConstr.cmi
tactics/eqschemes.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi engine/uState.cmi engine/termops.cmi kernel/term.cmi \
    kernel/safe_typing.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    lib/pp.cmi kernel/names.cmi engine/namegen.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi pretyping/indrec.cmi \
    tactics/ind_tables.cmi library/globnames.cmi library/global.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declarations.cmo library/coqlib.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi tactics/eqschemes.cmi
tactics/eqschemes.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx engine/uState.cmx engine/termops.cmx kernel/term.cmx \
    kernel/safe_typing.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    lib/pp.cmx kernel/names.cmx engine/namegen.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx pretyping/indrec.cmx \
    tactics/ind_tables.cmx library/globnames.cmx library/global.cmx \
    engine/evd.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declarations.cmx library/coqlib.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx tactics/eqschemes.cmi
tactics/eqschemes.cmi : kernel/univ.cmi kernel/sorts.cmi \
    kernel/safe_typing.cmi kernel/names.cmi tactics/ind_tables.cmi \
    engine/evd.cmi kernel/environ.cmi kernel/constr.cmi
tactics/equality.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    pretyping/unification.cmi pretyping/typing.cmi engine/termops.cmi \
    kernel/term.cmi proofs/tactypes.cmo tactics/tactics.cmi \
    tactics/tacticals.cmi pretyping/tacred.cmi proofs/tacmach.cmi \
    kernel/sorts.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    engine/proofview.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    clib/option.cmi kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    proofs/logic.cmi pretyping/locusops.cmi pretyping/locus.cmo \
    library/libnames.cmi library/lib.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi pretyping/indrec.cmi \
    tactics/ind_tables.cmi lib/hook.cmi tactics/hipattern.cmi \
    library/goptions.cmi proofs/goal.cmi library/globnames.cmi \
    library/global.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarconv.cmi kernel/evar.cmi tactics/eqschemes.cmi \
    kernel/environ.cmi tactics/elimschemes.cmi engine/eConstr.cmi \
    kernel/declarations.cmo library/coqlib.cmi kernel/context.cmi \
    pretyping/constr_matching.cmi kernel/constr.cmi proofs/clenvtac.cmi \
    proofs/clenv.cmi lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    tactics/equality.cmi
tactics/equality.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    pretyping/unification.cmx pretyping/typing.cmx engine/termops.cmx \
    kernel/term.cmx proofs/tactypes.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx pretyping/tacred.cmx proofs/tacmach.cmx \
    kernel/sorts.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    engine/proofview.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    clib/option.cmx kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    proofs/logic.cmx pretyping/locusops.cmx pretyping/locus.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx pretyping/indrec.cmx \
    tactics/ind_tables.cmx lib/hook.cmx tactics/hipattern.cmx \
    library/goptions.cmx proofs/goal.cmx library/globnames.cmx \
    library/global.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarconv.cmx kernel/evar.cmx tactics/eqschemes.cmx \
    kernel/environ.cmx tactics/elimschemes.cmx engine/eConstr.cmx \
    kernel/declarations.cmx library/coqlib.cmx kernel/context.cmx \
    pretyping/constr_matching.cmx kernel/constr.cmx proofs/clenvtac.cmx \
    proofs/clenv.cmx lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    tactics/equality.cmi
tactics/equality.cmi : proofs/tactypes.cmo tactics/tactics.cmi \
    engine/proofview.cmi kernel/names.cmi pretyping/locus.cmo \
    tactics/ind_tables.cmi lib/hook.cmi engine/evd.cmi kernel/environ.cmi \
    engine/eConstr.cmi
tactics/hints.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi pretyping/typing.cmi pretyping/typeclasses.cmi \
    engine/termops.cmi kernel/term.cmi pretyping/tacred.cmi \
    library/summary.cmi interp/smartlocate.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi pretyping/recordops.cmi engine/proofview.cmi \
    proofs/proof_global.cmi proofs/proof.cmi printing/printer.cmi \
    pretyping/pretyping.cmi printing/pputils.cmi lib/pp.cmi proofs/pfedit.cmi \
    pretyping/patternops.cmi pretyping/pattern.cmo clib/option.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi kernel/mod_subst.cmi proofs/logic.cmi \
    library/libobject.cmi library/libnames.cmi library/lib.cmi clib/int.cmi \
    pretyping/inductiveops.cmi library/goptions.cmi proofs/goal.cmi \
    library/globnames.cmi library/global.cmi interp/genintern.cmi \
    lib/genarg.cmi lib/flags.cmi lib/feedback.cmi engine/evd.cmi \
    engine/evarutil.cmi kernel/environ.cmi engine/eConstr.cmi \
    interp/dumpglob.cmi kernel/declareops.cmi interp/declare.cmi \
    library/decl_kinds.cmo library/coqlib.cmi kernel/context.cmi \
    interp/constrintern.cmi interp/constrexpr.cmo kernel/constr.cmi \
    proofs/clenv.cmi lib/cWarnings.cmi clib/cString.cmi lib/cErrors.cmi \
    lib/cAst.cmi tactics/btermdn.cmi tactics/hints.cmi
tactics/hints.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx pretyping/typing.cmx pretyping/typeclasses.cmx \
    engine/termops.cmx kernel/term.cmx pretyping/tacred.cmx \
    library/summary.cmx interp/smartlocate.cmx pretyping/retyping.cmx \
    pretyping/reductionops.cmx pretyping/recordops.cmx engine/proofview.cmx \
    proofs/proof_global.cmx proofs/proof.cmx printing/printer.cmx \
    pretyping/pretyping.cmx printing/pputils.cmx lib/pp.cmx proofs/pfedit.cmx \
    pretyping/patternops.cmx pretyping/pattern.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx kernel/mod_subst.cmx proofs/logic.cmx \
    library/libobject.cmx library/libnames.cmx library/lib.cmx clib/int.cmx \
    pretyping/inductiveops.cmx library/goptions.cmx proofs/goal.cmx \
    library/globnames.cmx library/global.cmx interp/genintern.cmx \
    lib/genarg.cmx lib/flags.cmx lib/feedback.cmx engine/evd.cmx \
    engine/evarutil.cmx kernel/environ.cmx engine/eConstr.cmx \
    interp/dumpglob.cmx kernel/declareops.cmx interp/declare.cmx \
    library/decl_kinds.cmx library/coqlib.cmx kernel/context.cmx \
    interp/constrintern.cmx interp/constrexpr.cmx kernel/constr.cmx \
    proofs/clenv.cmx lib/cWarnings.cmx clib/cString.cmx lib/cErrors.cmx \
    lib/cAst.cmx tactics/btermdn.cmx tactics/hints.cmi
tactics/hints.cmi : lib/util.cmi kernel/univ.cmi pretyping/typeclasses.cmi \
    proofs/tactypes.cmo engine/proofview.cmi lib/pp.cmi pretyping/pattern.cmo \
    kernel/names.cmi library/libnames.cmi lib/genarg.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi library/decl_kinds.cmo \
    kernel/context.cmi interp/constrexpr.cmo proofs/clenv.cmi
tactics/hipattern.cmo : kernel/vars.cmi lib/util.cmi engine/termops.cmi \
    kernel/term.cmi proofs/tacmach.cmi pretyping/reductionops.cmi lib/pp.cmi \
    pretyping/patternops.cmi clib/option.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi library/library.cmi clib/int.cmi \
    pretyping/inductiveops.cmi library/globnames.cmi library/global.cmi \
    pretyping/glob_term.cmo engine/evd.cmi engine/evar_kinds.cmi \
    engine/eConstr.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    lib/dAst.cmi library/coqlib.cmi kernel/context.cmi \
    pretyping/constr_matching.cmi kernel/constr.cmi lib/cErrors.cmi \
    tactics/hipattern.cmi
tactics/hipattern.cmx : kernel/vars.cmx lib/util.cmx engine/termops.cmx \
    kernel/term.cmx proofs/tacmach.cmx pretyping/reductionops.cmx lib/pp.cmx \
    pretyping/patternops.cmx clib/option.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx library/library.cmx clib/int.cmx \
    pretyping/inductiveops.cmx library/globnames.cmx library/global.cmx \
    pretyping/glob_term.cmx engine/evd.cmx engine/evar_kinds.cmx \
    engine/eConstr.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    lib/dAst.cmx library/coqlib.cmx kernel/context.cmx \
    pretyping/constr_matching.cmx kernel/constr.cmx lib/cErrors.cmx \
    tactics/hipattern.cmi
tactics/hipattern.cmi : engine/proofview.cmi kernel/names.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi library/coqlib.cmi
tactics/ind_tables.cmo : lib/util.cmi engine/univSubst.cmi kernel/univ.cmi \
    engine/uState.cmi library/summary.cmi kernel/safe_typing.cmi lib/pp.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi kernel/mod_subst.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi clib/int.cmi library/global.cmi \
    lib/future.cmi engine/evd.cmi kernel/entries.cmo kernel/declareops.cmi \
    interp/declare.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    kernel/constr.cmi lib/cErrors.cmi tactics/ind_tables.cmi
tactics/ind_tables.cmx : lib/util.cmx engine/univSubst.cmx kernel/univ.cmx \
    engine/uState.cmx library/summary.cmx kernel/safe_typing.cmx lib/pp.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx kernel/mod_subst.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx library/global.cmx \
    lib/future.cmx engine/evd.cmx kernel/entries.cmx kernel/declareops.cmx \
    interp/declare.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    kernel/constr.cmx lib/cErrors.cmx tactics/ind_tables.cmi
tactics/ind_tables.cmi : kernel/safe_typing.cmi lib/pp.cmi kernel/names.cmi \
    engine/evd.cmi interp/declare.cmi kernel/constr.cmi
tactics/inv.cmo : kernel/vars.cmi lib/util.cmi pretyping/unification.cmi \
    pretyping/typing.cmi engine/termops.cmi kernel/term.cmi \
    proofs/tactypes.cmo tactics/tactics.cmi tactics/tacticals.cmi \
    pretyping/tacred.cmi proofs/tacmach.cmi pretyping/retyping.cmi \
    proofs/refine.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    printing/printer.cmi lib/pp.cmi kernel/names.cmi engine/namegen.cmi \
    proofs/miscprint.cmi proofs/logic.cmi lib/loc.cmi clib/int.cmi \
    pretyping/inductiveops.cmi pretyping/indrec.cmi engine/evd.cmi \
    engine/evarutil.cmi tactics/equality.cmi tactics/elim.cmi \
    engine/eConstr.cmi library/coqlib.cmi kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi lib/cAst.cmi tactics/inv.cmi
tactics/inv.cmx : kernel/vars.cmx lib/util.cmx pretyping/unification.cmx \
    pretyping/typing.cmx engine/termops.cmx kernel/term.cmx \
    proofs/tactypes.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    pretyping/tacred.cmx proofs/tacmach.cmx pretyping/retyping.cmx \
    proofs/refine.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    printing/printer.cmx lib/pp.cmx kernel/names.cmx engine/namegen.cmx \
    proofs/miscprint.cmx proofs/logic.cmx lib/loc.cmx clib/int.cmx \
    pretyping/inductiveops.cmx pretyping/indrec.cmx engine/evd.cmx \
    engine/evarutil.cmx tactics/equality.cmx tactics/elim.cmx \
    engine/eConstr.cmx library/coqlib.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx lib/cAst.cmx tactics/inv.cmi
tactics/inv.cmi : proofs/tactypes.cmo engine/proofview.cmi kernel/names.cmi \
    engine/eConstr.cmi
tactics/leminv.cmo : kernel/vars.cmi lib/util.cmi pretyping/unification.cmi \
    engine/termops.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    proofs/proof.cmi printing/printer.cmi lib/pp.cmi kernel/names.cmi \
    engine/namegen.cmi pretyping/inductiveops.cmi library/global.cmi \
    engine/evd.cmi engine/evarutil.cmi kernel/environ.cmi kernel/entries.cmo \
    engine/eConstr.cmi interp/declare.cmi library/decl_kinds.cmo \
    kernel/context.cmi interp/constrintern.cmi kernel/constr.cmi \
    proofs/clenvtac.cmi proofs/clenv.cmi lib/cErrors.cmi tactics/leminv.cmi
tactics/leminv.cmx : kernel/vars.cmx lib/util.cmx pretyping/unification.cmx \
    engine/termops.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    proofs/proof.cmx printing/printer.cmx lib/pp.cmx kernel/names.cmx \
    engine/namegen.cmx pretyping/inductiveops.cmx library/global.cmx \
    engine/evd.cmx engine/evarutil.cmx kernel/environ.cmx kernel/entries.cmx \
    engine/eConstr.cmx interp/declare.cmx library/decl_kinds.cmx \
    kernel/context.cmx interp/constrintern.cmx kernel/constr.cmx \
    proofs/clenvtac.cmx proofs/clenv.cmx lib/cErrors.cmx tactics/leminv.cmi
tactics/leminv.cmi : proofs/tactypes.cmo kernel/sorts.cmi \
    engine/proofview.cmi kernel/names.cmi engine/eConstr.cmi \
    interp/constrexpr.cmo
tactics/tacticals.cmo : lib/util.cmi pretyping/unification.cmi \
    engine/termops.cmi kernel/term.cmi proofs/tactypes.cmo proofs/tacmach.cmi \
    pretyping/retyping.cmi proofs/refiner.cmi kernel/reduction.cmi \
    engine/proofview.cmi printing/printer.cmi pretyping/pretype_errors.cmi \
    lib/pp.cmi clib/option.cmi kernel/names.cmi engine/namegen.cmi \
    pretyping/locusops.cmi lib/loc.cmi clib/int.cmi pretyping/indrec.cmi \
    proofs/goal_select.cmi library/global.cmi clib/exninfo.cmi engine/evd.cmi \
    engine/eConstr.cmi kernel/declareops.cmi kernel/declarations.cmo \
    kernel/context.cmi kernel/constr.cmi proofs/clenvtac.cmi proofs/clenv.cmi \
    lib/cErrors.cmi lib/cAst.cmi tactics/tacticals.cmi
tactics/tacticals.cmx : lib/util.cmx pretyping/unification.cmx \
    engine/termops.cmx kernel/term.cmx proofs/tactypes.cmx proofs/tacmach.cmx \
    pretyping/retyping.cmx proofs/refiner.cmx kernel/reduction.cmx \
    engine/proofview.cmx printing/printer.cmx pretyping/pretype_errors.cmx \
    lib/pp.cmx clib/option.cmx kernel/names.cmx engine/namegen.cmx \
    pretyping/locusops.cmx lib/loc.cmx clib/int.cmx pretyping/indrec.cmx \
    proofs/goal_select.cmx library/global.cmx clib/exninfo.cmx engine/evd.cmx \
    engine/eConstr.cmx kernel/declareops.cmx kernel/declarations.cmx \
    kernel/context.cmx kernel/constr.cmx proofs/clenvtac.cmx proofs/clenv.cmx \
    lib/cErrors.cmx lib/cAst.cmx tactics/tacticals.cmi
tactics/tacticals.cmi : lib/util.cmi proofs/tactypes.cmo kernel/sorts.cmi \
    engine/proofview.cmi proofs/proof_type.cmo lib/pp.cmi kernel/names.cmi \
    pretyping/locus.cmo lib/loc.cmi proofs/goal_select.cmi engine/evd.cmi \
    engine/eConstr.cmi kernel/constr.cmi
tactics/tactics.cmo : kernel/vars.cmi lib/util.cmi engine/univProblem.cmi \
    kernel/univ.cmi pretyping/unification.cmi pretyping/typing.cmi \
    pretyping/typeclasses.cmi engine/termops.cmi kernel/term.cmi \
    proofs/tactypes.cmo tactics/tacticals.cmi pretyping/tacred.cmi \
    proofs/tacmach.cmi kernel/sorts.cmi kernel/safe_typing.cmi \
    pretyping/retyping.cmi proofs/refiner.cmi proofs/refine.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi proofs/redexpr.cmi \
    pretyping/recordops.cmi engine/proofview.cmi proofs/proof_global.cmi \
    printing/printer.cmi pretyping/pretyping.cmi pretyping/pretype_errors.cmi \
    printing/pputils.cmi lib/pp.cmi proofs/pfedit.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi proofs/miscprint.cmi pretyping/ltac_pretype.cmo \
    engine/logic_monad.cmi proofs/logic.cmi pretyping/locusops.cmi \
    pretyping/locus.cmo lib/loc.cmi clib/int.cmi pretyping/inductiveops.cmi \
    pretyping/indrec.cmi interp/impargs.cmi lib/hook.cmi \
    tactics/hipattern.cmi library/goptions.cmi library/globnames.cmi \
    library/global.cmi interp/genredexpr.cmo lib/future.cmi \
    pretyping/find_subterm.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarsolve.cmi pretyping/evardefine.cmi pretyping/evarconv.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    pretyping/detyping.cmi interp/declare.cmi kernel/declarations.cmo \
    library/decl_kinds.cmo library/coqlib.cmi kernel/conv_oracle.cmi \
    kernel/context.cmi interp/constrintern.cmi pretyping/constr_matching.cmi \
    kernel/constr.cmi proofs/clenvtac.cmi proofs/clenv.cmi lib/cWarnings.cmi \
    lib/cErrors.cmi lib/cAst.cmi tactics/tactics.cmi
tactics/tactics.cmx : kernel/vars.cmx lib/util.cmx engine/univProblem.cmx \
    kernel/univ.cmx pretyping/unification.cmx pretyping/typing.cmx \
    pretyping/typeclasses.cmx engine/termops.cmx kernel/term.cmx \
    proofs/tactypes.cmx tactics/tacticals.cmx pretyping/tacred.cmx \
    proofs/tacmach.cmx kernel/sorts.cmx kernel/safe_typing.cmx \
    pretyping/retyping.cmx proofs/refiner.cmx proofs/refine.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx proofs/redexpr.cmx \
    pretyping/recordops.cmx engine/proofview.cmx proofs/proof_global.cmx \
    printing/printer.cmx pretyping/pretyping.cmx pretyping/pretype_errors.cmx \
    printing/pputils.cmx lib/pp.cmx proofs/pfedit.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx proofs/miscprint.cmx pretyping/ltac_pretype.cmx \
    engine/logic_monad.cmx proofs/logic.cmx pretyping/locusops.cmx \
    pretyping/locus.cmx lib/loc.cmx clib/int.cmx pretyping/inductiveops.cmx \
    pretyping/indrec.cmx interp/impargs.cmx lib/hook.cmx \
    tactics/hipattern.cmx library/goptions.cmx library/globnames.cmx \
    library/global.cmx interp/genredexpr.cmx lib/future.cmx \
    pretyping/find_subterm.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarsolve.cmx pretyping/evardefine.cmx pretyping/evarconv.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    pretyping/detyping.cmx interp/declare.cmx kernel/declarations.cmx \
    library/decl_kinds.cmx library/coqlib.cmx kernel/conv_oracle.cmx \
    kernel/context.cmx interp/constrintern.cmx pretyping/constr_matching.cmx \
    kernel/constr.cmx proofs/clenvtac.cmx proofs/clenv.cmx lib/cWarnings.cmx \
    lib/cErrors.cmx lib/cAst.cmx tactics/tactics.cmi
tactics/tactics.cmi : pretyping/unification.cmi proofs/tactypes.cmo \
    pretyping/reductionops.cmi proofs/redexpr.cmi engine/proofview.cmi \
    proofs/proof_type.cmo pretyping/pattern.cmo kernel/names.cmi \
    pretyping/ltac_pretype.cmo proofs/logic.cmi pretyping/locus.cmo \
    lib/hook.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo library/coqlib.cmi interp/constrexpr.cmo \
    kernel/constr.cmi proofs/clenv.cmi lib/cAst.cmi
tactics/term_dnet.cmo : lib/util.cmi engine/termops.cmi kernel/reduction.cmi \
    lib/pp.cmi clib/option.cmi kernel/names.cmi kernel/mod_subst.cmi \
    clib/int.cmi library/globnames.cmi engine/evd.cmi kernel/evar.cmi \
    engine/eConstr.cmi tactics/dnet.cmi kernel/constr.cmi \
    tactics/term_dnet.cmi
tactics/term_dnet.cmx : lib/util.cmx engine/termops.cmx kernel/reduction.cmx \
    lib/pp.cmx clib/option.cmx kernel/names.cmx kernel/mod_subst.cmx \
    clib/int.cmx library/globnames.cmx engine/evd.cmx kernel/evar.cmx \
    engine/eConstr.cmx tactics/dnet.cmx kernel/constr.cmx \
    tactics/term_dnet.cmi
tactics/term_dnet.cmi : kernel/mod_subst.cmi kernel/constr.cmi
tools/coq_makefile.cmo : clib/option.cmi lib/feedback.cmi lib/envars.cmi \
    config/coq_config.cmi lib/coqProject_file.cmi clib/cUnix.cmi \
    clib/cString.cmi clib/cList.cmi
tools/coq_makefile.cmx : clib/option.cmx lib/feedback.cmx lib/envars.cmx \
    config/coq_config.cmx lib/coqProject_file.cmx clib/cUnix.cmx \
    clib/cString.cmx clib/cList.cmx
tools/coq_tex.cmo :
tools/coq_tex.cmx :
tools/coqc.cmo : toplevel/usage.cmi lib/envars.cmi config/coq_config.cmi \
    clib/cList.cmi
tools/coqc.cmx : toplevel/usage.cmx lib/envars.cmx config/coq_config.cmx \
    clib/cList.cmx
tools/coqdep.cmo : lib/system.cmi clib/minisys.cmo lib/flags.cmi \
    lib/envars.cmi tools/coqdep_lexer.cmi tools/coqdep_common.cmi \
    config/coq_config.cmi lib/coqProject_file.cmi
tools/coqdep.cmx : lib/system.cmx clib/minisys.cmx lib/flags.cmx \
    lib/envars.cmx tools/coqdep_lexer.cmx tools/coqdep_common.cmx \
    config/coq_config.cmx lib/coqProject_file.cmx
tools/coqdep_boot.cmo : tools/coqdep_common.cmi
tools/coqdep_boot.cmx : tools/coqdep_common.cmx
tools/coqdep_common.cmo : clib/minisys.cmo tools/coqdep_lexer.cmi \
    tools/coqdep_common.cmi
tools/coqdep_common.cmx : clib/minisys.cmx tools/coqdep_lexer.cmx \
    tools/coqdep_common.cmi
tools/coqdep_common.cmi :
tools/coqdep_lexer.cmo : clib/unicode.cmi tools/coqdep_lexer.cmi
tools/coqdep_lexer.cmx : clib/unicode.cmx tools/coqdep_lexer.cmi
tools/coqdep_lexer.cmi :
tools/coqdoc/alpha.cmo : tools/coqdoc/cdglobals.cmi tools/coqdoc/alpha.cmi
tools/coqdoc/alpha.cmx : tools/coqdoc/cdglobals.cmx tools/coqdoc/alpha.cmi
tools/coqdoc/alpha.cmi :
tools/coqdoc/cdglobals.cmo : config/coq_config.cmi \
    tools/coqdoc/cdglobals.cmi
tools/coqdoc/cdglobals.cmx : config/coq_config.cmx \
    tools/coqdoc/cdglobals.cmi
tools/coqdoc/cdglobals.cmi :
tools/coqdoc/cpretty.cmo : tools/coqdoc/tokens.cmi tools/coqdoc/output.cmi \
    tools/coqdoc/index.cmi tools/coqdoc/cdglobals.cmi \
    tools/coqdoc/cpretty.cmi
tools/coqdoc/cpretty.cmx : tools/coqdoc/tokens.cmx tools/coqdoc/output.cmx \
    tools/coqdoc/index.cmx tools/coqdoc/cdglobals.cmx \
    tools/coqdoc/cpretty.cmi
tools/coqdoc/cpretty.cmi : tools/coqdoc/cdglobals.cmi
tools/coqdoc/index.cmo : tools/coqdoc/cdglobals.cmi tools/coqdoc/alpha.cmi \
    tools/coqdoc/index.cmi
tools/coqdoc/index.cmx : tools/coqdoc/cdglobals.cmx tools/coqdoc/alpha.cmx \
    tools/coqdoc/index.cmi
tools/coqdoc/index.cmi : tools/coqdoc/cdglobals.cmi
tools/coqdoc/main.cmo : tools/coqdoc/output.cmi tools/coqdoc/index.cmi \
    tools/coqdoc/cpretty.cmi config/coq_config.cmi tools/coqdoc/cdglobals.cmi
tools/coqdoc/main.cmx : tools/coqdoc/output.cmx tools/coqdoc/index.cmx \
    tools/coqdoc/cpretty.cmx config/coq_config.cmx tools/coqdoc/cdglobals.cmx
tools/coqdoc/output.cmo : tools/coqdoc/tokens.cmi tools/coqdoc/index.cmi \
    config/coq_config.cmi tools/coqdoc/cdglobals.cmi tools/coqdoc/output.cmi
tools/coqdoc/output.cmx : tools/coqdoc/tokens.cmx tools/coqdoc/index.cmx \
    config/coq_config.cmx tools/coqdoc/cdglobals.cmx tools/coqdoc/output.cmi
tools/coqdoc/output.cmi : tools/coqdoc/index.cmi tools/coqdoc/cdglobals.cmi
tools/coqdoc/tokens.cmo : tools/coqdoc/index.cmi tools/coqdoc/tokens.cmi
tools/coqdoc/tokens.cmx : tools/coqdoc/index.cmx tools/coqdoc/tokens.cmi
tools/coqdoc/tokens.cmi : tools/coqdoc/index.cmi
tools/coqwc.cmo :
tools/coqwc.cmx :
tools/coqworkmgr.cmo : stm/coqworkmgrApi.cmi
tools/coqworkmgr.cmx : stm/coqworkmgrApi.cmx
tools/fake_ide.cmo : ide/protocol/xmlprotocol.cmi \
    ide/protocol/xml_printer.cmi ide/protocol/xml_parser.cmi lib/util.cmi \
    lib/system.cmi lib/stateid.cmi lib/spawn.cmi lib/pp.cmi clib/option.cmi \
    ide/protocol/interface.cmo ide/document.cmi
tools/fake_ide.cmx : ide/protocol/xmlprotocol.cmx \
    ide/protocol/xml_printer.cmx ide/protocol/xml_parser.cmx lib/util.cmx \
    lib/system.cmx lib/stateid.cmx lib/spawn.cmx lib/pp.cmx clib/option.cmx \
    ide/protocol/interface.cmx ide/document.cmx
tools/md5sum.cmo :
tools/md5sum.cmx :
tools/mkwinapp.cmo :
tools/mkwinapp.cmx :
tools/ocamllibdep.cmo :
tools/ocamllibdep.cmx :
topbin/coqproofworker_bin.cmo : toplevel/workerLoop.cmi stm/stm.cmi \
    stm/asyncTaskQueue.cmi
topbin/coqproofworker_bin.cmx : toplevel/workerLoop.cmx stm/stm.cmx \
    stm/asyncTaskQueue.cmx
topbin/coqqueryworker_bin.cmo : toplevel/workerLoop.cmi stm/stm.cmi \
    stm/asyncTaskQueue.cmi
topbin/coqqueryworker_bin.cmx : toplevel/workerLoop.cmx stm/stm.cmx \
    stm/asyncTaskQueue.cmx
topbin/coqtacticworker_bin.cmo : toplevel/workerLoop.cmi stm/stm.cmi \
    stm/asyncTaskQueue.cmi
topbin/coqtacticworker_bin.cmx : toplevel/workerLoop.cmx stm/stm.cmx \
    stm/asyncTaskQueue.cmx
topbin/coqtop_bin.cmo : vernac/mltop.cmi toplevel/coqtop.cmi
topbin/coqtop_bin.cmx : vernac/mltop.cmx toplevel/coqtop.cmx
topbin/coqtop_byte_bin.cmo : lib/pp.cmi vernac/mltop.cmi toplevel/coqtop.cmi \
    lib/cErrors.cmi
topbin/coqtop_byte_bin.cmx : lib/pp.cmx vernac/mltop.cmx toplevel/coqtop.cmx \
    lib/cErrors.cmx
toplevel/coqargs.cmo : toplevel/usage.cmi vernac/topfmt.cmi lib/system.cmi \
    stm/stm.cmi stm/spawned.cmi printing/proof_diffs.cmi printing/printer.cmi \
    lib/pp.cmi kernel/nativelib.cmi kernel/names.cmi engine/namegen.cmi \
    vernac/mltop.cmi library/library.cmi library/libnames.cmi \
    kernel/indtypes.cmi library/global.cmi vernac/g_vernac.cmo lib/flags.cmi \
    lib/feedback.cmi kernel/environ.cmi lib/envars.cmi interp/dumpglob.cmi \
    kernel/declarations.cmo stm/coqworkmgrApi.cmi toplevel/coqinit.cmi \
    config/coq_config.cmi lib/cWarnings.cmi clib/cUnix.cmi clib/cString.cmi \
    lib/cErrors.cmi clib/backtrace.cmi toplevel/coqargs.cmi
toplevel/coqargs.cmx : toplevel/usage.cmx vernac/topfmt.cmx lib/system.cmx \
    stm/stm.cmx stm/spawned.cmx printing/proof_diffs.cmx printing/printer.cmx \
    lib/pp.cmx kernel/nativelib.cmx kernel/names.cmx engine/namegen.cmx \
    vernac/mltop.cmx library/library.cmx library/libnames.cmx \
    kernel/indtypes.cmx library/global.cmx vernac/g_vernac.cmx lib/flags.cmx \
    lib/feedback.cmx kernel/environ.cmx lib/envars.cmx interp/dumpglob.cmx \
    kernel/declarations.cmx stm/coqworkmgrApi.cmx toplevel/coqinit.cmx \
    config/coq_config.cmx lib/cWarnings.cmx clib/cUnix.cmx clib/cString.cmx \
    lib/cErrors.cmx clib/backtrace.cmx toplevel/coqargs.cmi
toplevel/coqargs.cmi : stm/stm.cmi kernel/names.cmi kernel/declarations.cmo
toplevel/coqinit.cmo : toplevel/vernac.cmi lib/util.cmi lib/pp.cmi \
    kernel/names.cmi vernac/mltop.cmi library/libnames.cmi lib/flags.cmi \
    lib/feedback.cmi lib/envars.cmi config/coq_config.cmi clib/cUnix.cmi \
    lib/cErrors.cmi clib/backtrace.cmi toplevel/coqinit.cmi
toplevel/coqinit.cmx : toplevel/vernac.cmx lib/util.cmx lib/pp.cmx \
    kernel/names.cmx vernac/mltop.cmx library/libnames.cmx lib/flags.cmx \
    lib/feedback.cmx lib/envars.cmx config/coq_config.cmx clib/cUnix.cmx \
    lib/cErrors.cmx clib/backtrace.cmx toplevel/coqinit.cmi
toplevel/coqinit.cmi : toplevel/vernac.cmi vernac/mltop.cmi
toplevel/coqloop.cmo : vernac/vernacexpr.cmo toplevel/vernac.cmi \
    vernac/topfmt.cmi parsing/tok.cmi stm/stm.cmi lib/stateid.cmi \
    proofs/proof_global.cmi proofs/proof.cmi printing/printer.cmi lib/pp.cmi \
    parsing/pcoq.cmi clib/option.cmi kernel/names.cmi vernac/mltop.cmi \
    lib/loc.cmi clib/int.cmi toplevel/g_toplevel.cmo lib/flags.cmi \
    lib/feedback.cmi clib/exninfo.cmi kernel/evar.cmi interp/dumpglob.cmi \
    toplevel/coqinit.cmi toplevel/coqargs.cmi config/coq_config.cmi \
    clib/cString.cmi clib/cList.cmi parsing/cLexer.cmi lib/cErrors.cmi \
    lib/cAst.cmi toplevel/coqloop.cmi
toplevel/coqloop.cmx : vernac/vernacexpr.cmx toplevel/vernac.cmx \
    vernac/topfmt.cmx parsing/tok.cmx stm/stm.cmx lib/stateid.cmx \
    proofs/proof_global.cmx proofs/proof.cmx printing/printer.cmx lib/pp.cmx \
    parsing/pcoq.cmx clib/option.cmx kernel/names.cmx vernac/mltop.cmx \
    lib/loc.cmx clib/int.cmx toplevel/g_toplevel.cmx lib/flags.cmx \
    lib/feedback.cmx clib/exninfo.cmx kernel/evar.cmx interp/dumpglob.cmx \
    toplevel/coqinit.cmx toplevel/coqargs.cmx config/coq_config.cmx \
    clib/cString.cmx clib/cList.cmx parsing/cLexer.cmx lib/cErrors.cmx \
    lib/cAst.cmx toplevel/coqloop.cmi
toplevel/coqloop.cmi : toplevel/vernac.cmi vernac/topfmt.cmi stm/stm.cmi \
    parsing/pcoq.cmi lib/feedback.cmi toplevel/coqargs.cmi
toplevel/coqtop.cmo : stm/vio_checking.cmi toplevel/vernac.cmi \
    vernac/topfmt.cmi clib/terminal.cmi stm/stm.cmi library/states.cmi \
    stm/spawned.cmi proofs/proof_global.cmi printing/proof_diffs.cmi \
    printing/prettyp.cmi lib/pp.cmi proofs/pfedit.cmi clib/option.cmi \
    kernel/names.cmi vernac/mltop.cmi library/loadpath.cmi \
    library/library.cmi library/lib.cmi library/global.cmi lib/flags.cmi \
    lib/feedback.cmi lib/envars.cmi interp/dumpglob.cmi stm/coqworkmgrApi.cmi \
    toplevel/coqloop.cmi toplevel/coqinit.cmi toplevel/coqargs.cmi \
    config/coq_config.cmi lib/cWarnings.cmi clib/cUnix.cmi lib/cProfile.cmi \
    clib/cObj.cmi clib/cList.cmi lib/cErrors.cmi lib/aux_file.cmi \
    toplevel/coqtop.cmi
toplevel/coqtop.cmx : stm/vio_checking.cmx toplevel/vernac.cmx \
    vernac/topfmt.cmx clib/terminal.cmx stm/stm.cmx library/states.cmx \
    stm/spawned.cmx proofs/proof_global.cmx printing/proof_diffs.cmx \
    printing/prettyp.cmx lib/pp.cmx proofs/pfedit.cmx clib/option.cmx \
    kernel/names.cmx vernac/mltop.cmx library/loadpath.cmx \
    library/library.cmx library/lib.cmx library/global.cmx lib/flags.cmx \
    lib/feedback.cmx lib/envars.cmx interp/dumpglob.cmx stm/coqworkmgrApi.cmx \
    toplevel/coqloop.cmx toplevel/coqinit.cmx toplevel/coqargs.cmx \
    config/coq_config.cmx lib/cWarnings.cmx clib/cUnix.cmx lib/cProfile.cmx \
    clib/cObj.cmx clib/cList.cmx lib/cErrors.cmx lib/aux_file.cmx \
    toplevel/coqtop.cmi
toplevel/coqtop.cmi : toplevel/vernac.cmi toplevel/coqargs.cmi
toplevel/g_toplevel.cmo : vernac/vernacexpr.cmo parsing/tok.cmi stm/stm.cmi \
    vernac/pvernac.cmi parsing/pcoq.cmi parsing/extend.cmo lib/cAst.cmi
toplevel/g_toplevel.cmx : vernac/vernacexpr.cmx parsing/tok.cmx stm/stm.cmx \
    vernac/pvernac.cmx parsing/pcoq.cmx parsing/extend.cmx lib/cAst.cmx
toplevel/usage.cmo : config/coq_config.cmi toplevel/usage.cmi
toplevel/usage.cmx : config/coq_config.cmx toplevel/usage.cmi
toplevel/usage.cmi :
toplevel/vernac.cmo : vernac/vernacprop.cmi vernac/vernacexpr.cmo \
    lib/util.cmi clib/unicode.cmi vernac/topfmt.cmi stm/stm.cmi \
    lib/stateid.cmi proofs/proof_global.cmi proofs/proof.cmi \
    vernac/ppvernac.cmi printing/pputils.cmi lib/pp.cmi parsing/pcoq.cmi \
    clib/option.cmi lib/loc.cmi lib/flags.cmi lib/feedback.cmi \
    lib/cErrors.cmi lib/cAst.cmi toplevel/vernac.cmi
toplevel/vernac.cmx : vernac/vernacprop.cmx vernac/vernacexpr.cmx \
    lib/util.cmx clib/unicode.cmx vernac/topfmt.cmx stm/stm.cmx \
    lib/stateid.cmx proofs/proof_global.cmx proofs/proof.cmx \
    vernac/ppvernac.cmx printing/pputils.cmx lib/pp.cmx parsing/pcoq.cmx \
    clib/option.cmx lib/loc.cmx lib/flags.cmx lib/feedback.cmx \
    lib/cErrors.cmx lib/cAst.cmx toplevel/vernac.cmi
toplevel/vernac.cmi : vernac/vernacexpr.cmo stm/stm.cmi lib/stateid.cmi \
    proofs/proof.cmi lib/cAst.cmi
toplevel/workerLoop.cmo : lib/flags.cmi stm/coqworkmgrApi.cmi \
    toplevel/coqtop.cmi toplevel/workerLoop.cmi
toplevel/workerLoop.cmx : lib/flags.cmx stm/coqworkmgrApi.cmx \
    toplevel/coqtop.cmx toplevel/workerLoop.cmi
toplevel/workerLoop.cmi :
vernac/assumptions.cmo : kernel/vars.cmi lib/util.cmi kernel/univ.cmi \
    kernel/term.cmi printing/printer.cmi lib/pp.cmi clib/option.cmi \
    kernel/names.cmi kernel/modops.cmi kernel/mod_subst.cmi \
    kernel/inductive.cmi library/globnames.cmi library/global.cmi \
    kernel/declareops.cmi kernel/declarations.cmo kernel/context.cmi \
    kernel/constr.cmi lib/cErrors.cmi clib/cArray.cmi vernac/assumptions.cmi
vernac/assumptions.cmx : kernel/vars.cmx lib/util.cmx kernel/univ.cmx \
    kernel/term.cmx printing/printer.cmx lib/pp.cmx clib/option.cmx \
    kernel/names.cmx kernel/modops.cmx kernel/mod_subst.cmx \
    kernel/inductive.cmx library/globnames.cmx library/global.cmx \
    kernel/declareops.cmx kernel/declarations.cmx kernel/context.cmx \
    kernel/constr.cmx lib/cErrors.cmx clib/cArray.cmx vernac/assumptions.cmi
vernac/assumptions.cmi : printing/printer.cmi kernel/names.cmi \
    library/globnames.cmi kernel/constr.cmi
vernac/auto_ind_decl.cmo : kernel/vars.cmi lib/util.cmi engine/univGen.cmi \
    kernel/univ.cmi engine/uState.cmi engine/termops.cmi kernel/term.cmi \
    proofs/tactypes.cmo tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi kernel/sorts.cmi kernel/safe_typing.cmi \
    pretyping/reductionops.cmi engine/proofview.cmi printing/printer.cmi \
    lib/pp.cmi proofs/pfedit.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi pretyping/locus.cmo clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi tactics/ind_tables.cmi \
    library/globnames.cmi library/global.cmi engine/evd.cmi \
    tactics/equality.cmi kernel/environ.cmi engine/eConstr.cmi \
    interp/declare.cmi kernel/declarations.cmo library/coqlib.cmi \
    kernel/context.cmi kernel/constr.cmi lib/cErrors.cmi lib/cAst.cmi \
    tactics/auto.cmi vernac/auto_ind_decl.cmi
vernac/auto_ind_decl.cmx : kernel/vars.cmx lib/util.cmx engine/univGen.cmx \
    kernel/univ.cmx engine/uState.cmx engine/termops.cmx kernel/term.cmx \
    proofs/tactypes.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx kernel/sorts.cmx kernel/safe_typing.cmx \
    pretyping/reductionops.cmx engine/proofview.cmx printing/printer.cmx \
    lib/pp.cmx proofs/pfedit.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx pretyping/locus.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx tactics/ind_tables.cmx \
    library/globnames.cmx library/global.cmx engine/evd.cmx \
    tactics/equality.cmx kernel/environ.cmx engine/eConstr.cmx \
    interp/declare.cmx kernel/declarations.cmx library/coqlib.cmx \
    kernel/context.cmx kernel/constr.cmx lib/cErrors.cmx lib/cAst.cmx \
    tactics/auto.cmx vernac/auto_ind_decl.cmi
vernac/auto_ind_decl.cmi : kernel/names.cmi tactics/ind_tables.cmi
vernac/class.cmo : kernel/vars.cmi lib/util.cmi pretyping/typing.cmi \
    engine/termops.cmi kernel/term.cmi pretyping/reductionops.cmi \
    pretyping/recordops.cmi printing/printer.cmi lib/pp.cmi clib/option.cmi \
    library/nametab.cmi kernel/names.cmi engine/namegen.cmi vernac/lemmas.cmi \
    clib/int.cmi library/globnames.cmi library/global.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi kernel/environ.cmi kernel/entries.cmo \
    engine/eConstr.cmi interp/declare.cmi library/decl_kinds.cmo \
    kernel/context.cmi kernel/constr.cmi pretyping/classops.cmi \
    lib/cWarnings.cmi lib/cErrors.cmi vernac/class.cmi
vernac/class.cmx : kernel/vars.cmx lib/util.cmx pretyping/typing.cmx \
    engine/termops.cmx kernel/term.cmx pretyping/reductionops.cmx \
    pretyping/recordops.cmx printing/printer.cmx lib/pp.cmx clib/option.cmx \
    library/nametab.cmx kernel/names.cmx engine/namegen.cmx vernac/lemmas.cmx \
    clib/int.cmx library/globnames.cmx library/global.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx kernel/environ.cmx kernel/entries.cmx \
    engine/eConstr.cmx interp/declare.cmx library/decl_kinds.cmx \
    kernel/context.cmx kernel/constr.cmx pretyping/classops.cmx \
    lib/cWarnings.cmx lib/cErrors.cmx vernac/class.cmi
vernac/class.cmi : kernel/names.cmi vernac/lemmas.cmi library/decl_kinds.cmo \
    pretyping/classops.cmi
vernac/classes.cmo : kernel/vars.cmi lib/util.cmi engine/univops.cmi \
    engine/univNames.cmi kernel/univ.cmi pretyping/typeclasses_errors.cmi \
    pretyping/typeclasses.cmi engine/termops.cmi kernel/term.cmi \
    tactics/tactics.cmi tactics/tacticals.cmi proofs/refine.cmi \
    engine/proofview.cmi pretyping/pretyping.cmi lib/pp.cmi proofs/pfedit.cmi \
    clib/option.cmi vernac/obligations.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    library/libnames.cmi library/lib.cmi vernac/lemmas.cmi \
    interp/implicit_quantifiers.cmi interp/impargs.cmi lib/hook.cmi \
    tactics/hints.cmi library/goptions.cmi library/globnames.cmi \
    library/global.cmi lib/flags.cmi engine/evd.cmi engine/evarutil.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    interp/dumpglob.cmi library/declaremods.cmi vernac/declareDef.cmi \
    interp/declare.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    kernel/context.cmi interp/constrintern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo vernac/comAssumption.cmi clib/cList.cmi \
    lib/cErrors.cmi lib/cAst.cmi vernac/classes.cmi
vernac/classes.cmx : kernel/vars.cmx lib/util.cmx engine/univops.cmx \
    engine/univNames.cmx kernel/univ.cmx pretyping/typeclasses_errors.cmx \
    pretyping/typeclasses.cmx engine/termops.cmx kernel/term.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx proofs/refine.cmx \
    engine/proofview.cmx pretyping/pretyping.cmx lib/pp.cmx proofs/pfedit.cmx \
    clib/option.cmx vernac/obligations.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    library/libnames.cmx library/lib.cmx vernac/lemmas.cmx \
    interp/implicit_quantifiers.cmx interp/impargs.cmx lib/hook.cmx \
    tactics/hints.cmx library/goptions.cmx library/globnames.cmx \
    library/global.cmx lib/flags.cmx engine/evd.cmx engine/evarutil.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    interp/dumpglob.cmx library/declaremods.cmx vernac/declareDef.cmx \
    interp/declare.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    kernel/context.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx vernac/comAssumption.cmx clib/cList.cmx \
    lib/cErrors.cmx lib/cAst.cmx vernac/classes.cmi
vernac/classes.cmi : vernac/vernacexpr.cmo engine/uState.cmi \
    pretyping/typeclasses.cmi engine/proofview.cmi kernel/names.cmi \
    library/libnames.cmi interp/impargs.cmi tactics/hints.cmi engine/evd.cmi \
    kernel/environ.cmi library/decl_kinds.cmo interp/constrexpr.cmo \
    kernel/constr.cmi
vernac/comAssumption.cmo : kernel/vars.cmi lib/util.cmi engine/univops.cmi \
    engine/univGen.cmi kernel/univ.cmi pretyping/typeclasses.cmi \
    proofs/proof_global.cmi pretyping/pretyping.cmi lib/pp.cmi \
    kernel/names.cmi library/lib.cmi interp/impargs.cmi library/goptions.cmi \
    library/globnames.cmi library/global.cmi lib/flags.cmi lib/feedback.cmi \
    engine/evd.cmi kernel/entries.cmo engine/eConstr.cmi \
    library/declaremods.cmi vernac/declareDef.cmi interp/declare.cmi \
    library/decl_kinds.cmo kernel/context.cmi interp/constrintern.cmi \
    interp/constrexpr_ops.cmi vernac/class.cmi lib/cErrors.cmi lib/cAst.cmi \
    vernac/comAssumption.cmi
vernac/comAssumption.cmx : kernel/vars.cmx lib/util.cmx engine/univops.cmx \
    engine/univGen.cmx kernel/univ.cmx pretyping/typeclasses.cmx \
    proofs/proof_global.cmx pretyping/pretyping.cmx lib/pp.cmx \
    kernel/names.cmx library/lib.cmx interp/impargs.cmx library/goptions.cmx \
    library/globnames.cmx library/global.cmx lib/flags.cmx lib/feedback.cmx \
    engine/evd.cmx kernel/entries.cmx engine/eConstr.cmx \
    library/declaremods.cmx vernac/declareDef.cmx interp/declare.cmx \
    library/decl_kinds.cmx kernel/context.cmx interp/constrintern.cmx \
    interp/constrexpr_ops.cmx vernac/class.cmx lib/cErrors.cmx lib/cAst.cmx \
    vernac/comAssumption.cmi
vernac/comAssumption.cmi : vernac/vernacexpr.cmo engine/univNames.cmi \
    kernel/univ.cmi kernel/names.cmi interp/impargs.cmi kernel/entries.cmo \
    library/declaremods.cmi library/decl_kinds.cmo interp/constrexpr.cmo \
    kernel/constr.cmi lib/cAst.cmi
vernac/comDefinition.cmo : lib/util.cmi kernel/univ.cmi engine/termops.cmi \
    kernel/term.cmi kernel/safe_typing.cmi pretyping/retyping.cmi \
    proofs/redexpr.cmi pretyping/pretyping.cmi lib/pp.cmi clib/option.cmi \
    vernac/obligations.cmi vernac/lemmas.cmi interp/impargs.cmi \
    library/global.cmi lib/future.cmi engine/evd.cmi kernel/entries.cmo \
    engine/eConstr.cmi vernac/declareDef.cmi interp/declare.cmi \
    kernel/context.cmi interp/constrintern.cmi interp/constrexpr_ops.cmi \
    lib/cWarnings.cmi vernac/comDefinition.cmi
vernac/comDefinition.cmx : lib/util.cmx kernel/univ.cmx engine/termops.cmx \
    kernel/term.cmx kernel/safe_typing.cmx pretyping/retyping.cmx \
    proofs/redexpr.cmx pretyping/pretyping.cmx lib/pp.cmx clib/option.cmx \
    vernac/obligations.cmx vernac/lemmas.cmx interp/impargs.cmx \
    library/global.cmx lib/future.cmx engine/evd.cmx kernel/entries.cmx \
    engine/eConstr.cmx vernac/declareDef.cmx interp/declare.cmx \
    kernel/context.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    lib/cWarnings.cmx vernac/comDefinition.cmi
vernac/comDefinition.cmi : engine/uState.cmi kernel/safe_typing.cmi \
    proofs/redexpr.cmi kernel/names.cmi vernac/lemmas.cmi interp/impargs.cmi \
    engine/evd.cmi kernel/entries.cmo library/decl_kinds.cmo \
    interp/constrexpr.cmo
vernac/comFixpoint.cmo : kernel/vars.cmi lib/util.cmi engine/univops.cmi \
    engine/uState.cmi pretyping/typing.cmi engine/termops.cmi \
    tactics/tactics.cmi tactics/tacticals.cmi kernel/safe_typing.cmi \
    pretyping/pretyping.cmi lib/pp.cmi clib/option.cmi kernel/names.cmi \
    vernac/metasyntax.cmi vernac/lemmas.cmi interp/impargs.cmi \
    library/global.cmi lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi \
    pretyping/evarconv.cmi kernel/environ.cmi engine/eConstr.cmi \
    vernac/declareDef.cmi interp/declare.cmi kernel/declarations.cmo \
    library/decl_kinds.cmo library/coqlib.cmi kernel/context.cmi \
    interp/constrintern.cmi interp/constrexpr_ops.cmi interp/constrexpr.cmo \
    kernel/constr.cmi lib/cWarnings.cmi clib/cList.cmi lib/cErrors.cmi \
    lib/cAst.cmi vernac/comFixpoint.cmi
vernac/comFixpoint.cmx : kernel/vars.cmx lib/util.cmx engine/univops.cmx \
    engine/uState.cmx pretyping/typing.cmx engine/termops.cmx \
    tactics/tactics.cmx tactics/tacticals.cmx kernel/safe_typing.cmx \
    pretyping/pretyping.cmx lib/pp.cmx clib/option.cmx kernel/names.cmx \
    vernac/metasyntax.cmx vernac/lemmas.cmx interp/impargs.cmx \
    library/global.cmx lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx \
    pretyping/evarconv.cmx kernel/environ.cmx engine/eConstr.cmx \
    vernac/declareDef.cmx interp/declare.cmx kernel/declarations.cmx \
    library/decl_kinds.cmx library/coqlib.cmx kernel/context.cmx \
    interp/constrintern.cmx interp/constrexpr_ops.cmx interp/constrexpr.cmx \
    kernel/constr.cmx lib/cWarnings.cmx clib/cList.cmx lib/cErrors.cmx \
    lib/cAst.cmx vernac/comFixpoint.cmi
vernac/comFixpoint.cmi : vernac/vernacexpr.cmo engine/uState.cmi \
    proofs/proof_global.cmi kernel/names.cmi interp/impargs.cmi \
    engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo kernel/context.cmi interp/constrexpr.cmo \
    kernel/constr.cmi
vernac/comInductive.cmo : lib/util.cmi kernel/univ.cmi engine/termops.cmi \
    kernel/term.cmi kernel/sorts.cmi pretyping/retyping.cmi \
    pretyping/reductionops.cmi kernel/reduction.cmi pretyping/pretyping.cmi \
    lib/pp.cmi clib/option.cmi library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi vernac/metasyntax.cmi lib/loc.cmi library/libnames.cmi \
    clib/int.cmi pretyping/inferCumulativity.cmi kernel/indtypes.cmi \
    vernac/indschemes.cmi interp/implicit_quantifiers.cmi interp/impargs.cmi \
    library/globnames.cmi library/global.cmi pretyping/glob_term.cmo \
    lib/flags.cmi lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    interp/declare.cmi kernel/declarations.cmo lib/dAst.cmi \
    kernel/context.cmi interp/constrintern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo kernel/constr.cmi vernac/class.cmi clib/cList.cmi \
    lib/cErrors.cmi lib/cAst.cmi vernac/comInductive.cmi
vernac/comInductive.cmx : lib/util.cmx kernel/univ.cmx engine/termops.cmx \
    kernel/term.cmx kernel/sorts.cmx pretyping/retyping.cmx \
    pretyping/reductionops.cmx kernel/reduction.cmx pretyping/pretyping.cmx \
    lib/pp.cmx clib/option.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx vernac/metasyntax.cmx lib/loc.cmx library/libnames.cmx \
    clib/int.cmx pretyping/inferCumulativity.cmx kernel/indtypes.cmx \
    vernac/indschemes.cmx interp/implicit_quantifiers.cmx interp/impargs.cmx \
    library/globnames.cmx library/global.cmx pretyping/glob_term.cmx \
    lib/flags.cmx lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    interp/declare.cmx kernel/declarations.cmx lib/dAst.cmx \
    kernel/context.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx kernel/constr.cmx vernac/class.cmx clib/cList.cmx \
    lib/cErrors.cmx lib/cAst.cmx vernac/comInductive.cmi
vernac/comInductive.cmi : vernac/vernacexpr.cmo engine/univNames.cmi \
    kernel/names.cmi library/libnames.cmi interp/impargs.cmi \
    kernel/entries.cmo kernel/declarations.cmo library/decl_kinds.cmo \
    interp/constrexpr.cmo
vernac/comProgramFixpoint.cmo : kernel/vars.cmi lib/util.cmi \
    engine/univNames.cmi pretyping/typing.cmi pretyping/typeclasses.cmi \
    engine/termops.cmi kernel/sorts.cmi pretyping/reductionops.cmi \
    printing/printer.cmi pretyping/pretyping.cmi lib/pp.cmi clib/option.cmi \
    vernac/obligations.cmi kernel/names.cmi engine/nameops.cmi lib/loc.cmi \
    library/libnames.cmi vernac/lemmas.cmi kernel/inductive.cmi \
    interp/impargs.cmi library/globnames.cmi library/global.cmi \
    lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi engine/evar_kinds.cmi \
    kernel/evar.cmi kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    interp/declare.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    library/coqlib.cmi kernel/context.cmi interp/constrintern.cmi \
    interp/constrexpr_ops.cmi interp/constrexpr.cmo kernel/constr.cmi \
    vernac/comFixpoint.cmi lib/cErrors.cmi lib/cAst.cmi \
    vernac/comProgramFixpoint.cmi
vernac/comProgramFixpoint.cmx : kernel/vars.cmx lib/util.cmx \
    engine/univNames.cmx pretyping/typing.cmx pretyping/typeclasses.cmx \
    engine/termops.cmx kernel/sorts.cmx pretyping/reductionops.cmx \
    printing/printer.cmx pretyping/pretyping.cmx lib/pp.cmx clib/option.cmx \
    vernac/obligations.cmx kernel/names.cmx engine/nameops.cmx lib/loc.cmx \
    library/libnames.cmx vernac/lemmas.cmx kernel/inductive.cmx \
    interp/impargs.cmx library/globnames.cmx library/global.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx engine/evar_kinds.cmx \
    kernel/evar.cmx kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    interp/declare.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    library/coqlib.cmx kernel/context.cmx interp/constrintern.cmx \
    interp/constrexpr_ops.cmx interp/constrexpr.cmx kernel/constr.cmx \
    vernac/comFixpoint.cmx lib/cErrors.cmx lib/cAst.cmx \
    vernac/comProgramFixpoint.cmi
vernac/comProgramFixpoint.cmi : vernac/vernacexpr.cmo library/decl_kinds.cmo
vernac/declareDef.cmo : proofs/proof_global.cmi lib/pp.cmi kernel/names.cmi \
    library/lib.cmi vernac/lemmas.cmi interp/impargs.cmi \
    library/globnames.cmi lib/future.cmi kernel/entries.cmo \
    interp/declare.cmi library/decl_kinds.cmo lib/cWarnings.cmi \
    vernac/declareDef.cmi
vernac/declareDef.cmx : proofs/proof_global.cmx lib/pp.cmx kernel/names.cmx \
    library/lib.cmx vernac/lemmas.cmx interp/impargs.cmx \
    library/globnames.cmx lib/future.cmx kernel/entries.cmx \
    interp/declare.cmx library/decl_kinds.cmx lib/cWarnings.cmx \
    vernac/declareDef.cmi
vernac/declareDef.cmi : engine/univNames.cmi kernel/safe_typing.cmi \
    kernel/names.cmi vernac/lemmas.cmi interp/impargs.cmi kernel/entries.cmo \
    library/decl_kinds.cmo kernel/constr.cmi
vernac/egramcoq.cmo : lib/util.cmi parsing/tok.cmi library/summary.cmi \
    lib/pp.cmi parsing/pcoq.cmi clib/option.cmi parsing/notation_gram.cmo \
    kernel/names.cmi lib/loc.cmi library/libnames.cmi clib/int.cmi \
    parsing/extend.cmo interp/constrexpr.cmo kernel/constr.cmi \
    lib/cErrors.cmi lib/cAst.cmi vernac/egramcoq.cmi
vernac/egramcoq.cmx : lib/util.cmx parsing/tok.cmx library/summary.cmx \
    lib/pp.cmx parsing/pcoq.cmx clib/option.cmx parsing/notation_gram.cmx \
    kernel/names.cmx lib/loc.cmx library/libnames.cmx clib/int.cmx \
    parsing/extend.cmx interp/constrexpr.cmx kernel/constr.cmx \
    lib/cErrors.cmx lib/cAst.cmx vernac/egramcoq.cmi
vernac/egramcoq.cmi : parsing/notation_gram.cmo
vernac/egramml.cmo : vernac/vernacexpr.cmo lib/util.cmi vernac/pvernac.cmi \
    parsing/pcoq.cmi clib/option.cmi lib/loc.cmi clib/int.cmi lib/genarg.cmi \
    parsing/extend.cmo parsing/cLexer.cmi vernac/egramml.cmi
vernac/egramml.cmx : vernac/vernacexpr.cmx lib/util.cmx vernac/pvernac.cmx \
    parsing/pcoq.cmx clib/option.cmx lib/loc.cmx clib/int.cmx lib/genarg.cmx \
    parsing/extend.cmx parsing/cLexer.cmx vernac/egramml.cmi
vernac/egramml.cmi : vernac/vernacexpr.cmo parsing/pcoq.cmi lib/loc.cmi \
    lib/genarg.cmi parsing/extend.cmo
vernac/explainErr.cmo : lib/util.cmi engine/univNames.cmi kernel/univ.cmi \
    pretyping/typeclasses_errors.cmi kernel/type_errors.cmi \
    pretyping/tacred.cmi proofs/refiner.cmi pretyping/pretype_errors.cmi \
    lib/pp.cmi clib/option.cmi interp/notation.cmi library/nametab.cmi \
    kernel/modops.cmi interp/modintern.cmi engine/logic_monad.cmi \
    proofs/logic.cmi lib/loc.cmi library/libnames.cmi clib/int.cmi \
    kernel/indtypes.cmi pretyping/indrec.cmi interp/implicit_quantifiers.cmi \
    vernac/himsg.cmi engine/evd.cmi engine/eConstr.cmi \
    interp/constrextern.cmi pretyping/cases.cmi clib/cList.cmi \
    parsing/cLexer.cmi lib/cErrors.cmi vernac/explainErr.cmi
vernac/explainErr.cmx : lib/util.cmx engine/univNames.cmx kernel/univ.cmx \
    pretyping/typeclasses_errors.cmx kernel/type_errors.cmx \
    pretyping/tacred.cmx proofs/refiner.cmx pretyping/pretype_errors.cmx \
    lib/pp.cmx clib/option.cmx interp/notation.cmx library/nametab.cmx \
    kernel/modops.cmx interp/modintern.cmx engine/logic_monad.cmx \
    proofs/logic.cmx lib/loc.cmx library/libnames.cmx clib/int.cmx \
    kernel/indtypes.cmx pretyping/indrec.cmx interp/implicit_quantifiers.cmx \
    vernac/himsg.cmx engine/evd.cmx engine/eConstr.cmx \
    interp/constrextern.cmx pretyping/cases.cmx clib/cList.cmx \
    parsing/cLexer.cmx lib/cErrors.cmx vernac/explainErr.cmi
vernac/explainErr.cmi : lib/util.cmi lib/pp.cmi lib/loc.cmi
vernac/g_proofs.cmo : vernac/vernacexpr.cmo parsing/tok.cmi \
    vernac/pvernac.cmi proofs/proof_global.cmi lib/pp.cmi parsing/pcoq.cmi \
    kernel/names.cmi tactics/hints.cmi pretyping/glob_term.cmo \
    vernac/g_vernac.cmo parsing/extend.cmo library/decl_kinds.cmo \
    interp/constrexpr.cmo lib/cWarnings.cmi lib/cAst.cmi
vernac/g_proofs.cmx : vernac/vernacexpr.cmx parsing/tok.cmx \
    vernac/pvernac.cmx proofs/proof_global.cmx lib/pp.cmx parsing/pcoq.cmx \
    kernel/names.cmx tactics/hints.cmx pretyping/glob_term.cmx \
    vernac/g_vernac.cmx parsing/extend.cmx library/decl_kinds.cmx \
    interp/constrexpr.cmx lib/cWarnings.cmx lib/cAst.cmx
vernac/g_vernac.cmo : vernac/vernacexpr.cmo lib/util.cmi kernel/univ.cmi \
    engine/uState.cmi pretyping/typeclasses.cmi parsing/tok.cmi \
    vernac/pvernac.cmi proofs/proof_bullet.cmi lib/pp.cmi parsing/pcoq.cmi \
    clib/option.cmi interp/notation_term.cmo kernel/names.cmi \
    engine/namegen.cmi pretyping/glob_term.cmo interp/genredexpr.cmo \
    lib/flags.cmi parsing/extend.cmo library/declaremods.cmi \
    kernel/declarations.cmo library/decl_kinds.cmo kernel/conv_oracle.cmi \
    interp/constrexpr_ops.cmi interp/constrexpr.cmo kernel/constr.cmi \
    lib/cWarnings.cmi parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi
vernac/g_vernac.cmx : vernac/vernacexpr.cmx lib/util.cmx kernel/univ.cmx \
    engine/uState.cmx pretyping/typeclasses.cmx parsing/tok.cmx \
    vernac/pvernac.cmx proofs/proof_bullet.cmx lib/pp.cmx parsing/pcoq.cmx \
    clib/option.cmx interp/notation_term.cmx kernel/names.cmx \
    engine/namegen.cmx pretyping/glob_term.cmx interp/genredexpr.cmx \
    lib/flags.cmx parsing/extend.cmx library/declaremods.cmx \
    kernel/declarations.cmx library/decl_kinds.cmx kernel/conv_oracle.cmx \
    interp/constrexpr_ops.cmx interp/constrexpr.cmx kernel/constr.cmx \
    lib/cWarnings.cmx parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx
vernac/himsg.cmo : kernel/vars.cmi lib/util.cmi engine/univNames.cmi \
    kernel/univ.cmi pretyping/typeclasses_errors.cmi \
    pretyping/typeclasses.cmi kernel/type_errors.cmi engine/termops.cmi \
    pretyping/tacred.cmi pretyping/reductionops.cmi printing/printer.cmi \
    pretyping/pretype_errors.cmi printing/ppconstr.cmi lib/pp.cmi \
    clib/option.cmi interp/notation.cmi library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi kernel/modops.cmi \
    interp/modintern.cmi proofs/logic.cmi pretyping/locus.cmo \
    library/libnames.cmi clib/int.cmi kernel/indtypes.cmi \
    pretyping/indrec.cmi library/global.cmi lib/flags.cmi engine/evd.cmi \
    engine/evarutil.cmi pretyping/evardefine.cmi engine/evar_kinds.cmi \
    kernel/evar.cmi kernel/environ.cmi engine/eConstr.cmi \
    kernel/declarations.cmo config/coq_config.cmi kernel/context.cmi \
    interp/constrextern.cmi interp/constrexpr_ops.cmi kernel/constr.cmi \
    pretyping/cases.cmi lib/cErrors.cmi lib/cAst.cmi vernac/himsg.cmi
vernac/himsg.cmx : kernel/vars.cmx lib/util.cmx engine/univNames.cmx \
    kernel/univ.cmx pretyping/typeclasses_errors.cmx \
    pretyping/typeclasses.cmx kernel/type_errors.cmx engine/termops.cmx \
    pretyping/tacred.cmx pretyping/reductionops.cmx printing/printer.cmx \
    pretyping/pretype_errors.cmx printing/ppconstr.cmx lib/pp.cmx \
    clib/option.cmx interp/notation.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx kernel/modops.cmx \
    interp/modintern.cmx proofs/logic.cmx pretyping/locus.cmx \
    library/libnames.cmx clib/int.cmx kernel/indtypes.cmx \
    pretyping/indrec.cmx library/global.cmx lib/flags.cmx engine/evd.cmx \
    engine/evarutil.cmx pretyping/evardefine.cmx engine/evar_kinds.cmx \
    kernel/evar.cmx kernel/environ.cmx engine/eConstr.cmx \
    kernel/declarations.cmx config/coq_config.cmx kernel/context.cmx \
    interp/constrextern.cmx interp/constrexpr_ops.cmx kernel/constr.cmx \
    pretyping/cases.cmx lib/cErrors.cmx lib/cAst.cmx vernac/himsg.cmi
vernac/himsg.cmi : pretyping/typeclasses_errors.cmi kernel/type_errors.cmi \
    pretyping/tacred.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    interp/notation.cmi kernel/modops.cmi interp/modintern.cmi \
    proofs/logic.cmi kernel/indtypes.cmi pretyping/indrec.cmi engine/evd.cmi \
    kernel/environ.cmi interp/constrexpr.cmo kernel/constr.cmi \
    pretyping/cases.cmi
vernac/indschemes.cmo : vernac/vernacexpr.cmo lib/util.cmi \
    engine/univGen.cmi kernel/univ.cmi engine/uState.cmi kernel/typeops.cmi \
    engine/termops.cmi kernel/term.cmi kernel/sorts.cmi \
    interp/smartlocate.cmi kernel/safe_typing.cmi pretyping/retyping.cmi \
    printing/printer.cmi lib/pp.cmi library/nametab.cmi kernel/names.cmi \
    engine/nameops.cmi library/libnames.cmi clib/int.cmi \
    pretyping/inductiveops.cmi kernel/inductive.cmi pretyping/indrec.cmi \
    tactics/ind_tables.cmi tactics/hipattern.cmi library/goptions.cmi \
    library/globnames.cmi library/global.cmi lib/future.cmi lib/flags.cmi \
    lib/feedback.cmi engine/evd.cmi engine/evarutil.cmi tactics/eqschemes.cmi \
    kernel/entries.cmo tactics/elimschemes.cmi engine/eConstr.cmi \
    interp/declare.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    library/coqlib.cmi kernel/context.cmi kernel/constr.cmi lib/cWarnings.cmi \
    lib/cErrors.cmi lib/cAst.cmi vernac/auto_ind_decl.cmi \
    vernac/indschemes.cmi
vernac/indschemes.cmx : vernac/vernacexpr.cmx lib/util.cmx \
    engine/univGen.cmx kernel/univ.cmx engine/uState.cmx kernel/typeops.cmx \
    engine/termops.cmx kernel/term.cmx kernel/sorts.cmx \
    interp/smartlocate.cmx kernel/safe_typing.cmx pretyping/retyping.cmx \
    printing/printer.cmx lib/pp.cmx library/nametab.cmx kernel/names.cmx \
    engine/nameops.cmx library/libnames.cmx clib/int.cmx \
    pretyping/inductiveops.cmx kernel/inductive.cmx pretyping/indrec.cmx \
    tactics/ind_tables.cmx tactics/hipattern.cmx library/goptions.cmx \
    library/globnames.cmx library/global.cmx lib/future.cmx lib/flags.cmx \
    lib/feedback.cmx engine/evd.cmx engine/evarutil.cmx tactics/eqschemes.cmx \
    kernel/entries.cmx tactics/elimschemes.cmx engine/eConstr.cmx \
    interp/declare.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    library/coqlib.cmx kernel/context.cmx kernel/constr.cmx lib/cWarnings.cmx \
    lib/cErrors.cmx lib/cAst.cmx vernac/auto_ind_decl.cmx \
    vernac/indschemes.cmi
vernac/indschemes.cmi : vernac/vernacexpr.cmo kernel/sorts.cmi \
    kernel/names.cmi engine/evd.cmi kernel/environ.cmi kernel/constr.cmi
vernac/lemmas.cmo : vernac/vernacexpr.cmo kernel/vars.cmi lib/util.cmi \
    kernel/univ.cmi engine/uState.cmi engine/termops.cmi tactics/tactics.cmi \
    tactics/tacticals.cmi kernel/safe_typing.cmi pretyping/reductionops.cmi \
    vernac/proof_using.cmi proofs/proof_global.cmi proofs/proof.cmi \
    printing/printer.cmi pretyping/pretyping.cmi lib/pp.cmi proofs/pfedit.cmi \
    clib/option.cmi library/nametab.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi library/lib.cmi library/kindops.cmi clib/int.cmi \
    interp/impargs.cmi library/goptions.cmi library/globnames.cmi \
    library/global.cmi lib/future.cmi lib/flags.cmi lib/feedback.cmi \
    engine/evd.cmi engine/evarutil.cmi kernel/environ.cmi kernel/entries.cmo \
    engine/eConstr.cmi library/decls.cmi kernel/declareops.cmi \
    interp/declare.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    kernel/context.cmi interp/constrintern.cmi interp/constrexpr_ops.cmi \
    kernel/constr.cmi lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    vernac/lemmas.cmi
vernac/lemmas.cmx : vernac/vernacexpr.cmx kernel/vars.cmx lib/util.cmx \
    kernel/univ.cmx engine/uState.cmx engine/termops.cmx tactics/tactics.cmx \
    tactics/tacticals.cmx kernel/safe_typing.cmx pretyping/reductionops.cmx \
    vernac/proof_using.cmx proofs/proof_global.cmx proofs/proof.cmx \
    printing/printer.cmx pretyping/pretyping.cmx lib/pp.cmx proofs/pfedit.cmx \
    clib/option.cmx library/nametab.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx library/lib.cmx library/kindops.cmx clib/int.cmx \
    interp/impargs.cmx library/goptions.cmx library/globnames.cmx \
    library/global.cmx lib/future.cmx lib/flags.cmx lib/feedback.cmx \
    engine/evd.cmx engine/evarutil.cmx kernel/environ.cmx kernel/entries.cmx \
    engine/eConstr.cmx library/decls.cmx kernel/declareops.cmx \
    interp/declare.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    kernel/context.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    kernel/constr.cmx lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    vernac/lemmas.cmi
vernac/lemmas.cmi : vernac/vernacexpr.cmo engine/uState.cmi \
    engine/proofview.cmi proofs/proof_global.cmi proofs/proof.cmi \
    pretyping/pretyping.cmi kernel/names.cmi interp/impargs.cmi \
    lib/future.cmi engine/evd.cmi kernel/environ.cmi engine/eConstr.cmi \
    library/decl_kinds.cmo
vernac/locality.cmo : lib/pp.cmi library/lib.cmi library/decl_kinds.cmo \
    lib/cErrors.cmi vernac/locality.cmi
vernac/locality.cmx : lib/pp.cmx library/lib.cmx library/decl_kinds.cmx \
    lib/cErrors.cmx vernac/locality.cmi
vernac/locality.cmi : library/decl_kinds.cmo
vernac/metasyntax.cmo : vernac/vernacexpr.cmo lib/util.cmi parsing/tok.cmi \
    interp/syntax_def.cmi vernac/pvernac.cmi vernac/ppvernac.cmi \
    parsing/ppextend.cmi lib/pp.cmi parsing/pcoq.cmi clib/option.cmi \
    parsing/notgram_ops.cmi interp/notation_term.cmo interp/notation_ops.cmi \
    parsing/notation_gram.cmo interp/notation.cmi kernel/names.cmi \
    engine/nameops.cmi engine/namegen.cmi lib/loc.cmi library/libobject.cmi \
    library/libnames.cmi library/lib.cmi clib/int.cmi lib/flags.cmi \
    lib/feedback.cmi parsing/extend.cmo vernac/egramcoq.cmi \
    interp/dumpglob.cmi interp/constrintern.cmi interp/constrexpr_ops.cmi \
    interp/constrexpr.cmo lib/cWarnings.cmi parsing/cLexer.cmi \
    lib/cErrors.cmi lib/cAst.cmi clib/bigint.cmi vernac/metasyntax.cmi
vernac/metasyntax.cmx : vernac/vernacexpr.cmx lib/util.cmx parsing/tok.cmx \
    interp/syntax_def.cmx vernac/pvernac.cmx vernac/ppvernac.cmx \
    parsing/ppextend.cmx lib/pp.cmx parsing/pcoq.cmx clib/option.cmx \
    parsing/notgram_ops.cmx interp/notation_term.cmx interp/notation_ops.cmx \
    parsing/notation_gram.cmx interp/notation.cmx kernel/names.cmx \
    engine/nameops.cmx engine/namegen.cmx lib/loc.cmx library/libobject.cmx \
    library/libnames.cmx library/lib.cmx clib/int.cmx lib/flags.cmx \
    lib/feedback.cmx parsing/extend.cmx vernac/egramcoq.cmx \
    interp/dumpglob.cmx interp/constrintern.cmx interp/constrexpr_ops.cmx \
    interp/constrexpr.cmx lib/cWarnings.cmx parsing/cLexer.cmx \
    lib/cErrors.cmx lib/cAst.cmx clib/bigint.cmx vernac/metasyntax.cmi
vernac/metasyntax.cmi : vernac/vernacexpr.cmo lib/pp.cmi \
    interp/notation_term.cmo interp/notation.cmi kernel/names.cmi \
    lib/flags.cmi kernel/environ.cmi interp/constrintern.cmi \
    interp/constrexpr.cmo
vernac/misctypes.cmo : proofs/tactypes.cmo kernel/names.cmi \
    engine/namegen.cmi proofs/logic.cmi pretyping/locus.cmo \
    pretyping/glob_term.cmo tactics/equality.cmi interp/constrexpr.cmo \
    lib/cAst.cmi
vernac/misctypes.cmx : proofs/tactypes.cmx kernel/names.cmx \
    engine/namegen.cmx proofs/logic.cmx pretyping/locus.cmx \
    pretyping/glob_term.cmx tactics/equality.cmx interp/constrexpr.cmx \
    lib/cAst.cmx
vernac/mltop.cmo : vernac/vernacexpr.cmo lib/util.cmi clib/unicode.cmi \
    lib/system.cmi library/summary.cmi lib/pp.cmi clib/option.cmi \
    kernel/nativelib.cmi kernel/names.cmi library/loadpath.cmi \
    library/libobject.cmi library/lib.cmi clib/int.cmi lib/flags.cmi \
    lib/feedback.cmi clib/exninfo.cmi config/coq_config.cmi lib/cWarnings.cmi \
    clib/cUnix.cmi lib/cErrors.cmi vernac/mltop.cmi
vernac/mltop.cmx : vernac/vernacexpr.cmx lib/util.cmx clib/unicode.cmx \
    lib/system.cmx library/summary.cmx lib/pp.cmx clib/option.cmx \
    kernel/nativelib.cmx kernel/names.cmx library/loadpath.cmx \
    library/libobject.cmx library/lib.cmx clib/int.cmx lib/flags.cmx \
    lib/feedback.cmx clib/exninfo.cmx config/coq_config.cmx lib/cWarnings.cmx \
    clib/cUnix.cmx lib/cErrors.cmx vernac/mltop.cmi
vernac/mltop.cmi : vernac/vernacexpr.cmo lib/pp.cmi kernel/names.cmi
vernac/obligations.cmo : kernel/vars.cmi lib/util.cmi engine/univops.cmi \
    engine/univSubst.cmi engine/univNames.cmi engine/univGen.cmi \
    kernel/univ.cmi engine/uState.cmi engine/termops.cmi kernel/term.cmi \
    tactics/tacticals.cmi library/summary.cmi kernel/safe_typing.cmi \
    proofs/refiner.cmi pretyping/reductionops.cmi engine/proofview.cmi \
    proofs/proof_global.cmi pretyping/program.cmi printing/printer.cmi \
    pretyping/pretyping.cmi pretyping/pretype_errors.cmi lib/pp.cmi \
    proofs/pfedit.cmi clib/option.cmi interp/notation_term.cmo \
    kernel/names.cmi engine/nameops.cmi vernac/metasyntax.cmi \
    vernac/locality.cmi lib/loc.cmi library/libobject.cmi library/lib.cmi \
    vernac/lemmas.cmi clib/int.cmi pretyping/inductiveops.cmi lib/hook.cmi \
    tactics/hints.cmi library/goptions.cmi library/global.cmi lib/future.cmi \
    lib/flags.cmi lib/feedback.cmi vernac/explainErr.cmi engine/evd.cmi \
    engine/evarutil.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi kernel/entries.cmo engine/eConstr.cmi \
    library/decls.cmi vernac/declareDef.cmi interp/declare.cmi \
    library/decl_kinds.cmo library/coqlib.cmi kernel/context.cmi \
    interp/constrexpr.cmo kernel/constr.cmi lib/cErrors.cmi \
    clib/cEphemeron.cmi kernel/cClosure.cmi lib/cAst.cmi \
    vernac/obligations.cmi
vernac/obligations.cmx : kernel/vars.cmx lib/util.cmx engine/univops.cmx \
    engine/univSubst.cmx engine/univNames.cmx engine/univGen.cmx \
    kernel/univ.cmx engine/uState.cmx engine/termops.cmx kernel/term.cmx \
    tactics/tacticals.cmx library/summary.cmx kernel/safe_typing.cmx \
    proofs/refiner.cmx pretyping/reductionops.cmx engine/proofview.cmx \
    proofs/proof_global.cmx pretyping/program.cmx printing/printer.cmx \
    pretyping/pretyping.cmx pretyping/pretype_errors.cmx lib/pp.cmx \
    proofs/pfedit.cmx clib/option.cmx interp/notation_term.cmx \
    kernel/names.cmx engine/nameops.cmx vernac/metasyntax.cmx \
    vernac/locality.cmx lib/loc.cmx library/libobject.cmx library/lib.cmx \
    vernac/lemmas.cmx clib/int.cmx pretyping/inductiveops.cmx lib/hook.cmx \
    tactics/hints.cmx library/goptions.cmx library/global.cmx lib/future.cmx \
    lib/flags.cmx lib/feedback.cmx vernac/explainErr.cmx engine/evd.cmx \
    engine/evarutil.cmx engine/evar_kinds.cmx kernel/evar.cmx \
    kernel/environ.cmx kernel/entries.cmx engine/eConstr.cmx \
    library/decls.cmx vernac/declareDef.cmx interp/declare.cmx \
    library/decl_kinds.cmx library/coqlib.cmx kernel/context.cmx \
    interp/constrexpr.cmx kernel/constr.cmx lib/cErrors.cmx \
    clib/cEphemeron.cmx kernel/cClosure.cmx lib/cAst.cmx \
    vernac/obligations.cmi
vernac/obligations.cmi : engine/uState.cmi library/summary.cmi \
    engine/proofview.cmi lib/pp.cmi interp/notation_term.cmo kernel/names.cmi \
    lib/loc.cmi vernac/lemmas.cmi clib/int.cmi lib/hook.cmi lib/genarg.cmi \
    clib/exninfo.cmi engine/evd.cmi engine/evar_kinds.cmi kernel/evar.cmi \
    kernel/environ.cmi library/decl_kinds.cmo interp/constrexpr.cmo \
    kernel/constr.cmi
vernac/ppvernac.cmo : vernac/vernacexpr.cmo lib/util.cmi kernel/univ.cmi \
    engine/uState.cmi pretyping/typeclasses.cmi engine/termops.cmi \
    proofs/proof_global.cmi proofs/proof_bullet.cmi printing/pputils.cmi \
    printing/ppconstr.cmi lib/pp.cmi clib/option.cmi interp/notation_term.cmo \
    kernel/names.cmi engine/namegen.cmi lib/loc.cmi library/libnames.cmi \
    library/kindops.cmi clib/int.cmi tactics/hints.cmi proofs/goal_select.cmi \
    library/global.cmi lib/flags.cmi parsing/extend.cmo vernac/egramml.cmi \
    library/declaremods.cmi library/decl_kinds.cmo kernel/conv_oracle.cmi \
    interp/constrexpr_ops.cmi interp/constrexpr.cmo lib/cErrors.cmi \
    lib/cAst.cmi vernac/ppvernac.cmi
vernac/ppvernac.cmx : vernac/vernacexpr.cmx lib/util.cmx kernel/univ.cmx \
    engine/uState.cmx pretyping/typeclasses.cmx engine/termops.cmx \
    proofs/proof_global.cmx proofs/proof_bullet.cmx printing/pputils.cmx \
    printing/ppconstr.cmx lib/pp.cmx clib/option.cmx interp/notation_term.cmx \
    kernel/names.cmx engine/namegen.cmx lib/loc.cmx library/libnames.cmx \
    library/kindops.cmx clib/int.cmx tactics/hints.cmx proofs/goal_select.cmx \
    library/global.cmx lib/flags.cmx parsing/extend.cmx vernac/egramml.cmx \
    library/declaremods.cmx library/decl_kinds.cmx kernel/conv_oracle.cmx \
    interp/constrexpr_ops.cmx interp/constrexpr.cmx lib/cErrors.cmx \
    lib/cAst.cmx vernac/ppvernac.cmi
vernac/ppvernac.cmi : vernac/vernacexpr.cmo lib/pp.cmi parsing/extend.cmo
vernac/proof_using.cmo : vernac/vernacexpr.cmo lib/util.cmi \
    library/summary.cmi printing/printer.cmi vernac/ppvernac.cmi lib/pp.cmi \
    parsing/pcoq.cmi clib/option.cmi kernel/names.cmi library/goptions.cmi \
    vernac/g_vernac.cmo lib/flags.cmi lib/feedback.cmi kernel/environ.cmi \
    kernel/declarations.cmo kernel/context.cmi clib/cList.cmi lib/cAst.cmi \
    lib/aux_file.cmi vernac/proof_using.cmi
vernac/proof_using.cmx : vernac/vernacexpr.cmx lib/util.cmx \
    library/summary.cmx printing/printer.cmx vernac/ppvernac.cmx lib/pp.cmx \
    parsing/pcoq.cmx clib/option.cmx kernel/names.cmx library/goptions.cmx \
    vernac/g_vernac.cmx lib/flags.cmx lib/feedback.cmx kernel/environ.cmx \
    kernel/declarations.cmx kernel/context.cmx clib/cList.cmx lib/cAst.cmx \
    lib/aux_file.cmx vernac/proof_using.cmi
vernac/proof_using.cmi : vernac/vernacexpr.cmo kernel/names.cmi \
    kernel/environ.cmi kernel/constr.cmi
vernac/pvernac.cmo : parsing/tok.cmi interp/stdarg.cmi parsing/pcoq.cmi \
    parsing/extend.cmo vernac/pvernac.cmi
vernac/pvernac.cmx : parsing/tok.cmx interp/stdarg.cmx parsing/pcoq.cmx \
    parsing/extend.cmx vernac/pvernac.cmi
vernac/pvernac.cmi : vernac/vernacexpr.cmo parsing/pcoq.cmi lib/loc.cmi \
    tactics/hints.cmi interp/genredexpr.cmo
vernac/record.cmo : vernac/vernacexpr.cmo kernel/vars.cmi lib/util.cmi \
    engine/univNames.cmi kernel/univ.cmi clib/unicode.cmi \
    pretyping/typeclasses.cmi kernel/type_errors.cmi engine/termops.cmi \
    kernel/term.cmi library/states.cmi kernel/sorts.cmi \
    kernel/safe_typing.cmi pretyping/retyping.cmi pretyping/reductionops.cmi \
    pretyping/recordops.cmi printing/printer.cmi pretyping/pretyping.cmi \
    lib/pp.cmi clib/option.cmi kernel/names.cmi engine/nameops.cmi \
    engine/namegen.cmi vernac/metasyntax.cmi lib/loc.cmi \
    pretyping/inferCumulativity.cmi pretyping/inductiveops.cmi \
    kernel/inductive.cmi interp/impargs.cmi library/goptions.cmi \
    library/globnames.cmi library/global.cmi pretyping/glob_term.cmo \
    lib/future.cmi engine/evd.cmi kernel/environ.cmi kernel/entries.cmo \
    engine/eConstr.cmi kernel/declareops.cmi interp/declare.cmi \
    kernel/declarations.cmo library/decl_kinds.cmo kernel/context.cmi \
    interp/constrintern.cmi interp/constrexpr_ops.cmi interp/constrexpr.cmo \
    kernel/constr.cmi vernac/comInductive.cmi vernac/classes.cmi \
    vernac/class.cmi lib/cWarnings.cmi lib/cErrors.cmi lib/cAst.cmi \
    vernac/record.cmi
vernac/record.cmx : vernac/vernacexpr.cmx kernel/vars.cmx lib/util.cmx \
    engine/univNames.cmx kernel/univ.cmx clib/unicode.cmx \
    pretyping/typeclasses.cmx kernel/type_errors.cmx engine/termops.cmx \
    kernel/term.cmx library/states.cmx kernel/sorts.cmx \
    kernel/safe_typing.cmx pretyping/retyping.cmx pretyping/reductionops.cmx \
    pretyping/recordops.cmx printing/printer.cmx pretyping/pretyping.cmx \
    lib/pp.cmx clib/option.cmx kernel/names.cmx engine/nameops.cmx \
    engine/namegen.cmx vernac/metasyntax.cmx lib/loc.cmx \
    pretyping/inferCumulativity.cmx pretyping/inductiveops.cmx \
    kernel/inductive.cmx interp/impargs.cmx library/goptions.cmx \
    library/globnames.cmx library/global.cmx pretyping/glob_term.cmx \
    lib/future.cmx engine/evd.cmx kernel/environ.cmx kernel/entries.cmx \
    engine/eConstr.cmx kernel/declareops.cmx interp/declare.cmx \
    kernel/declarations.cmx library/decl_kinds.cmx kernel/context.cmx \
    interp/constrintern.cmx interp/constrexpr_ops.cmx interp/constrexpr.cmx \
    kernel/constr.cmx vernac/comInductive.cmx vernac/classes.cmx \
    vernac/class.cmx lib/cWarnings.cmx lib/cErrors.cmx lib/cAst.cmx \
    vernac/record.cmi
vernac/record.cmi : vernac/vernacexpr.cmo engine/univNames.cmi \
    kernel/names.cmi interp/impargs.cmi kernel/entries.cmo \
    kernel/declarations.cmo library/decl_kinds.cmo interp/constrexpr.cmo \
    kernel/constr.cmi
vernac/search.cmo : lib/util.cmi kernel/univ.cmi engine/termops.cmi \
    lib/pp.cmi proofs/pfedit.cmi pretyping/pattern.cmo library/nametab.cmi \
    kernel/names.cmi library/libobject.cmi library/libnames.cmi \
    pretyping/inductiveops.cmi clib/heap.cmi library/goptions.cmi \
    library/globnames.cmi library/global.cmi engine/evd.cmi \
    kernel/environ.cmi engine/eConstr.cmi kernel/declareops.cmi \
    library/declaremods.cmi kernel/declarations.cmo library/coqlib.cmi \
    kernel/context.cmi pretyping/constr_matching.cmi kernel/constr.cmi \
    clib/cSet.cmi vernac/search.cmi
vernac/search.cmx : lib/util.cmx kernel/univ.cmx engine/termops.cmx \
    lib/pp.cmx proofs/pfedit.cmx pretyping/pattern.cmx library/nametab.cmx \
    kernel/names.cmx library/libobject.cmx library/libnames.cmx \
    pretyping/inductiveops.cmx clib/heap.cmx library/goptions.cmx \
    library/globnames.cmx library/global.cmx engine/evd.cmx \
    kernel/environ.cmx engine/eConstr.cmx kernel/declareops.cmx \
    library/declaremods.cmx kernel/declarations.cmx library/coqlib.cmx \
    kernel/context.cmx pretyping/constr_matching.cmx kernel/constr.cmx \
    clib/cSet.cmx vernac/search.cmi
vernac/search.cmi : pretyping/pattern.cmo kernel/names.cmi \
    kernel/environ.cmi kernel/constr.cmi
vernac/topfmt.cmo : lib/util.cmi clib/terminal.cmi lib/pp.cmi \
    clib/option.cmi lib/loc.cmi lib/flags.cmi lib/feedback.cmi \
    clib/exninfo.cmi clib/cString.cmi lib/cErrors.cmi clib/backtrace.cmi \
    vernac/topfmt.cmi
vernac/topfmt.cmx : lib/util.cmx clib/terminal.cmx lib/pp.cmx \
    clib/option.cmx lib/loc.cmx lib/flags.cmx lib/feedback.cmx \
    clib/exninfo.cmx clib/cString.cmx lib/cErrors.cmx clib/backtrace.cmx \
    vernac/topfmt.cmi
vernac/topfmt.cmi : clib/terminal.cmi lib/pp.cmi lib/loc.cmi \
    lib/feedback.cmi
vernac/vernacentries.cmo : vernac/vernacstate.cmi vernac/vernacinterp.cmi \
    vernac/vernacexpr.cmo lib/util.cmi engine/univNames.cmi kernel/univ.cmi \
    engine/uState.cmi kernel/uGraph.cmi vernac/topfmt.cmi engine/termops.cmi \
    kernel/term.cmi tactics/tactics.cmi tactics/tacticals.cmi \
    proofs/tacmach.cmi lib/system.cmi library/states.cmi \
    interp/smartlocate.cmi vernac/search.cmi kernel/safe_typing.cmi \
    pretyping/retyping.cmi interp/reserve.cmi pretyping/reductionops.cmi \
    proofs/redexpr.cmi pretyping/recordops.cmi vernac/record.cmi \
    vernac/pvernac.cmi vernac/proof_using.cmi proofs/proof_global.cmi \
    proofs/proof_bullet.cmi proofs/proof.cmi printing/printmod.cmi \
    printing/printer.cmi printing/prettyp.cmi vernac/ppvernac.cmi lib/pp.cmi \
    proofs/pfedit.cmi parsing/pcoq.cmi pretyping/pattern.cmo clib/option.cmi \
    vernac/obligations.cmi interp/notation_term.cmo interp/notation_ops.cmi \
    interp/notation.cmi pretyping/nativenorm.cmi library/nametab.cmi \
    kernel/names.cmi engine/nameops.cmi engine/namegen.cmi \
    interp/modintern.cmi vernac/mltop.cmi vernac/metasyntax.cmi \
    engine/logic_monad.cmi proofs/logic.cmi vernac/locality.cmi lib/loc.cmi \
    library/loadpath.cmi library/library.cmi library/libnames.cmi \
    library/lib.cmi vernac/lemmas.cmi clib/int.cmi pretyping/inductiveops.cmi \
    vernac/indschemes.cmi interp/implicit_quantifiers.cmi interp/impargs.cmi \
    lib/hook.cmi tactics/hints.cmi library/goptions.cmi \
    proofs/goal_select.cmi proofs/goal.cmi library/globnames.cmi \
    library/global.cmi interp/genintern.cmi lib/genarg.cmi lib/flags.cmi \
    lib/feedback.cmi parsing/extend.cmo vernac/explainErr.cmi engine/evd.cmi \
    engine/evarutil.cmi pretyping/evarconv.cmi kernel/evar.cmi \
    kernel/environ.cmi lib/envars.cmi vernac/egramml.cmi engine/eConstr.cmi \
    interp/dumpglob.cmi pretyping/detyping.cmi library/declaremods.cmi \
    interp/declare.cmi kernel/declarations.cmo library/decl_kinds.cmo \
    kernel/conv_oracle.cmi lib/control.cmi kernel/context.cmi \
    interp/constrintern.cmi interp/constrextern.cmi interp/constrexpr.cmo \
    vernac/comProgramFixpoint.cmi vernac/comInductive.cmi \
    vernac/comFixpoint.cmi vernac/comDefinition.cmi vernac/comAssumption.cmi \
    pretyping/classops.cmi vernac/classes.cmi vernac/class.cmi \
    kernel/clambda.cmi kernel/cbytegen.cmi lib/cWarnings.cmi clib/cUnix.cmi \
    clib/cString.cmi parsing/cLexer.cmi lib/cErrors.cmi lib/cAst.cmi \
    lib/aux_file.cmi vernac/assumptions.cmi pretyping/arguments_renaming.cmi \
    vernac/vernacentries.cmi
vernac/vernacentries.cmx : vernac/vernacstate.cmx vernac/vernacinterp.cmx \
    vernac/vernacexpr.cmx lib/util.cmx engine/univNames.cmx kernel/univ.cmx \
    engine/uState.cmx kernel/uGraph.cmx vernac/topfmt.cmx engine/termops.cmx \
    kernel/term.cmx tactics/tactics.cmx tactics/tacticals.cmx \
    proofs/tacmach.cmx lib/system.cmx library/states.cmx \
    interp/smartlocate.cmx vernac/search.cmx kernel/safe_typing.cmx \
    pretyping/retyping.cmx interp/reserve.cmx pretyping/reductionops.cmx \
    proofs/redexpr.cmx pretyping/recordops.cmx vernac/record.cmx \
    vernac/pvernac.cmx vernac/proof_using.cmx proofs/proof_global.cmx \
    proofs/proof_bullet.cmx proofs/proof.cmx printing/printmod.cmx \
    printing/printer.cmx printing/prettyp.cmx vernac/ppvernac.cmx lib/pp.cmx \
    proofs/pfedit.cmx parsing/pcoq.cmx pretyping/pattern.cmx clib/option.cmx \
    vernac/obligations.cmx interp/notation_term.cmx interp/notation_ops.cmx \
    interp/notation.cmx pretyping/nativenorm.cmx library/nametab.cmx \
    kernel/names.cmx engine/nameops.cmx engine/namegen.cmx \
    interp/modintern.cmx vernac/mltop.cmx vernac/metasyntax.cmx \
    engine/logic_monad.cmx proofs/logic.cmx vernac/locality.cmx lib/loc.cmx \
    library/loadpath.cmx library/library.cmx library/libnames.cmx \
    library/lib.cmx vernac/lemmas.cmx clib/int.cmx pretyping/inductiveops.cmx \
    vernac/indschemes.cmx interp/implicit_quantifiers.cmx interp/impargs.cmx \
    lib/hook.cmx tactics/hints.cmx library/goptions.cmx \
    proofs/goal_select.cmx proofs/goal.cmx library/globnames.cmx \
    library/global.cmx interp/genintern.cmx lib/genarg.cmx lib/flags.cmx \
    lib/feedback.cmx parsing/extend.cmx vernac/explainErr.cmx engine/evd.cmx \
    engine/evarutil.cmx pretyping/evarconv.cmx kernel/evar.cmx \
    kernel/environ.cmx lib/envars.cmx vernac/egramml.cmx engine/eConstr.cmx \
    interp/dumpglob.cmx pretyping/detyping.cmx library/declaremods.cmx \
    interp/declare.cmx kernel/declarations.cmx library/decl_kinds.cmx \
    kernel/conv_oracle.cmx lib/control.cmx kernel/context.cmx \
    interp/constrintern.cmx interp/constrextern.cmx interp/constrexpr.cmx \
    vernac/comProgramFixpoint.cmx vernac/comInductive.cmx \
    vernac/comFixpoint.cmx vernac/comDefinition.cmx vernac/comAssumption.cmx \
    pretyping/classops.cmx vernac/classes.cmx vernac/class.cmx \
    kernel/clambda.cmx kernel/cbytegen.cmx lib/cWarnings.cmx clib/cUnix.cmx \
    clib/cString.cmx parsing/cLexer.cmx lib/cErrors.cmx lib/cAst.cmx \
    lib/aux_file.cmx vernac/assumptions.cmx pretyping/arguments_renaming.cmx \
    vernac/vernacentries.cmi
vernac/vernacentries.cmi : vernac/vernacstate.cmi vernac/vernacinterp.cmi \
    vernac/vernacexpr.cmo proofs/redexpr.cmi proofs/proof_global.cmi \
    proofs/proof.cmi parsing/pcoq.cmi library/libnames.cmi lib/hook.cmi \
    interp/genredexpr.cmo lib/genarg.cmi parsing/extend.cmo engine/evd.cmi \
    kernel/environ.cmi interp/constrexpr.cmo lib/cAst.cmi
vernac/vernacexpr.cmo : engine/univNames.cmi pretyping/typeclasses.cmi \
    kernel/sorts.cmi proofs/proof_global.cmi proofs/proof_bullet.cmi \
    interp/notation_term.cmo kernel/names.cmi library/libnames.cmi \
    tactics/hints.cmi library/goptions.cmi proofs/goal_select.cmi \
    pretyping/glob_term.cmo interp/genredexpr.cmo lib/genarg.cmi \
    lib/flags.cmi parsing/extend.cmo library/declaremods.cmi \
    kernel/declarations.cmo library/decl_kinds.cmo kernel/conv_oracle.cmi \
    interp/constrexpr.cmo lib/cAst.cmi
vernac/vernacexpr.cmx : engine/univNames.cmx pretyping/typeclasses.cmx \
    kernel/sorts.cmx proofs/proof_global.cmx proofs/proof_bullet.cmx \
    interp/notation_term.cmx kernel/names.cmx library/libnames.cmx \
    tactics/hints.cmx library/goptions.cmx proofs/goal_select.cmx \
    pretyping/glob_term.cmx interp/genredexpr.cmx lib/genarg.cmx \
    lib/flags.cmx parsing/extend.cmx library/declaremods.cmx \
    kernel/declarations.cmx library/decl_kinds.cmx kernel/conv_oracle.cmx \
    interp/constrexpr.cmx lib/cAst.cmx
vernac/vernacinterp.cmo : vernac/vernacstate.cmi vernac/vernacexpr.cmo \
    lib/util.cmi lib/pp.cmi lib/loc.cmi lib/genarg.cmi lib/flags.cmi \
    lib/feedback.cmi vernac/egramml.cmi lib/cWarnings.cmi lib/cErrors.cmi \
    vernac/vernacinterp.cmi
vernac/vernacinterp.cmx : vernac/vernacstate.cmx vernac/vernacexpr.cmx \
    lib/util.cmx lib/pp.cmx lib/loc.cmx lib/genarg.cmx lib/flags.cmx \
    lib/feedback.cmx vernac/egramml.cmx lib/cWarnings.cmx lib/cErrors.cmx \
    vernac/vernacinterp.cmi
vernac/vernacinterp.cmi : vernac/vernacstate.cmi vernac/vernacexpr.cmo \
    lib/loc.cmi lib/genarg.cmi
vernac/vernacprop.cmo : vernac/vernacexpr.cmo lib/cAst.cmi \
    vernac/vernacprop.cmi
vernac/vernacprop.cmx : vernac/vernacexpr.cmx lib/cAst.cmx \
    vernac/vernacprop.cmi
vernac/vernacprop.cmi : vernac/vernacexpr.cmo
vernac/vernacstate.cmo : library/states.cmi proofs/proof_global.cmi \
    vernac/vernacstate.cmi
vernac/vernacstate.cmx : library/states.cmx proofs/proof_global.cmx \
    vernac/vernacstate.cmi
vernac/vernacstate.cmi : library/summary.cmi library/states.cmi \
    proofs/proof_global.cmi

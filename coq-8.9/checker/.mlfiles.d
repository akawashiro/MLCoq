checker/analyze.cmo : checker/analyze.cmi
checker/analyze.cmx : checker/analyze.cmi
checker/analyze.cmi :
checker/check.cmo : checker/values.cmi checker/validate.cmi lib/util.cmi \
    checker/univ.cmi lib/system.cmi checker/safe_typing.cmi lib/pp.cmi \
    clib/option.cmi checker/names.cmi lib/future.cmi lib/flags.cmi \
    lib/feedback.cmi checker/declarations.cmi config/coq_config.cmi \
    checker/cic.cmi clib/cUnix.cmi lib/cErrors.cmi checker/analyze.cmi \
    checker/check.cmi
checker/check.cmx : checker/values.cmx checker/validate.cmx lib/util.cmx \
    checker/univ.cmx lib/system.cmx checker/safe_typing.cmx lib/pp.cmx \
    clib/option.cmx checker/names.cmx lib/future.cmx lib/flags.cmx \
    lib/feedback.cmx checker/declarations.cmx config/coq_config.cmx \
    checker/cic.cmi clib/cUnix.cmx lib/cErrors.cmx checker/analyze.cmx \
    checker/check.cmi
checker/check.cmi : checker/names.cmi clib/cUnix.cmi
checker/check_stat.cmo : checker/safe_typing.cmi lib/pp.cmi \
    checker/names.cmi checker/indtypes.cmi lib/feedback.cmi \
    checker/environ.cmi checker/declarations.cmi checker/cic.cmi \
    clib/cObj.cmi checker/check_stat.cmi
checker/check_stat.cmx : checker/safe_typing.cmx lib/pp.cmx \
    checker/names.cmx checker/indtypes.cmx lib/feedback.cmx \
    checker/environ.cmx checker/declarations.cmx checker/cic.cmi \
    clib/cObj.cmx checker/check_stat.cmi
checker/check_stat.cmi :
checker/checker.cmo : lib/util.cmi checker/univ.cmi checker/type_errors.cmi \
    lib/system.cmi checker/safe_typing.cmi checker/print.cmi lib/pp.cmi \
    checker/names.cmi checker/indtypes.cmi lib/flags.cmi lib/feedback.cmi \
    checker/environ.cmi lib/envars.cmi config/coq_config.cmi checker/cic.cmi \
    checker/check_stat.cmi checker/check.cmi lib/cErrors.cmi \
    checker/checker.cmi
checker/checker.cmx : lib/util.cmx checker/univ.cmx checker/type_errors.cmx \
    lib/system.cmx checker/safe_typing.cmx checker/print.cmx lib/pp.cmx \
    checker/names.cmx checker/indtypes.cmx lib/flags.cmx lib/feedback.cmx \
    checker/environ.cmx lib/envars.cmx config/coq_config.cmx checker/cic.cmi \
    checker/check_stat.cmx checker/check.cmx lib/cErrors.cmx \
    checker/checker.cmi
checker/checker.cmi :
checker/cic.cmi : checker/univ.cmi lib/rtree.cmi checker/names.cmi \
    lib/future.cmi
checker/closure.cmo : lib/util.cmi checker/univ.cmi checker/term.cmi \
    lib/pp.cmi checker/names.cmi clib/int.cmi clib/hashset.cmi \
    lib/feedback.cmi checker/esubst.cmi checker/environ.cmi \
    checker/declarations.cmi checker/cic.cmi checker/closure.cmi
checker/closure.cmx : lib/util.cmx checker/univ.cmx checker/term.cmx \
    lib/pp.cmx checker/names.cmx clib/int.cmx clib/hashset.cmx \
    lib/feedback.cmx checker/esubst.cmx checker/environ.cmx \
    checker/declarations.cmx checker/cic.cmi checker/closure.cmi
checker/closure.cmi : checker/names.cmi checker/esubst.cmi \
    checker/environ.cmi checker/cic.cmi
checker/declarations.cmo : lib/util.cmi checker/univ.cmi checker/term.cmi \
    lib/rtree.cmi clib/option.cmi checker/names.cmi checker/cic.cmi \
    checker/declarations.cmi
checker/declarations.cmx : lib/util.cmx checker/univ.cmx checker/term.cmx \
    lib/rtree.cmx clib/option.cmx checker/names.cmx checker/cic.cmi \
    checker/declarations.cmi
checker/declarations.cmi : checker/univ.cmi checker/names.cmi \
    checker/cic.cmi
checker/environ.cmo : lib/util.cmi checker/univ.cmi checker/term.cmi \
    lib/pp.cmi checker/names.cmi clib/int.cmi checker/declarations.cmi \
    checker/cic.cmi lib/cErrors.cmi checker/environ.cmi
checker/environ.cmx : lib/util.cmx checker/univ.cmx checker/term.cmx \
    lib/pp.cmx checker/names.cmx clib/int.cmx checker/declarations.cmx \
    checker/cic.cmi lib/cErrors.cmx checker/environ.cmi
checker/environ.cmi : checker/univ.cmi checker/names.cmi checker/cic.cmi
checker/esubst.cmo : lib/util.cmi clib/int.cmi clib/cArray.cmi \
    checker/esubst.cmi
checker/esubst.cmx : lib/util.cmx clib/int.cmx clib/cArray.cmx \
    checker/esubst.cmi
checker/esubst.cmo : lib/util.cmi clib/int.cmi clib/cArray.cmi \
    checker/esubst.cmi
checker/esubst.cmx : lib/util.cmx clib/int.cmx clib/cArray.cmx \
    checker/esubst.cmi
checker/esubst.cmi : lib/util.cmi
checker/esubst.cmi : lib/util.cmi
checker/indtypes.cmo : lib/util.cmi checker/univ.cmi checker/typeops.cmi \
    checker/term.cmi lib/rtree.cmi checker/reduction.cmi lib/pp.cmi \
    checker/names.cmi checker/inductive.cmi lib/flags.cmi lib/feedback.cmi \
    checker/environ.cmi checker/declarations.cmi checker/cic.cmi \
    lib/cErrors.cmi checker/indtypes.cmi
checker/indtypes.cmx : lib/util.cmx checker/univ.cmx checker/typeops.cmx \
    checker/term.cmx lib/rtree.cmx checker/reduction.cmx lib/pp.cmx \
    checker/names.cmx checker/inductive.cmx lib/flags.cmx lib/feedback.cmx \
    checker/environ.cmx checker/declarations.cmx checker/cic.cmi \
    lib/cErrors.cmx checker/indtypes.cmi
checker/indtypes.cmi : lib/pp.cmi checker/names.cmi checker/environ.cmi \
    checker/cic.cmi
checker/inductive.cmo : lib/util.cmi checker/univ.cmi \
    checker/type_errors.cmi checker/term.cmi lib/rtree.cmi \
    checker/reduction.cmi lib/pp.cmi checker/names.cmi clib/int.cmi \
    checker/environ.cmi checker/declarations.cmi checker/cic.cmi \
    lib/cErrors.cmi checker/inductive.cmi
checker/inductive.cmx : lib/util.cmx checker/univ.cmx \
    checker/type_errors.cmx checker/term.cmx lib/rtree.cmx \
    checker/reduction.cmx lib/pp.cmx checker/names.cmx clib/int.cmx \
    checker/environ.cmx checker/declarations.cmx checker/cic.cmi \
    lib/cErrors.cmx checker/inductive.cmi
checker/inductive.cmi : checker/univ.cmi checker/names.cmi \
    checker/environ.cmi checker/cic.cmi
checker/main.cmo : checker/checker.cmi checker/main.cmi
checker/main.cmx : checker/checker.cmx checker/main.cmi
checker/main.cmi :
checker/mod_checking.cmo : lib/util.cmi checker/univ.cmi checker/typeops.cmi \
    checker/subtyping.cmi checker/reduction.cmi lib/pp.cmi checker/names.cmi \
    checker/modops.cmi checker/indtypes.cmi lib/flags.cmi lib/feedback.cmi \
    checker/environ.cmi checker/declarations.cmi checker/cic.cmi \
    checker/mod_checking.cmi
checker/mod_checking.cmx : lib/util.cmx checker/univ.cmx checker/typeops.cmx \
    checker/subtyping.cmx checker/reduction.cmx lib/pp.cmx checker/names.cmx \
    checker/modops.cmx checker/indtypes.cmx lib/flags.cmx lib/feedback.cmx \
    checker/environ.cmx checker/declarations.cmx checker/cic.cmi \
    checker/mod_checking.cmi
checker/mod_checking.cmi : checker/names.cmi checker/environ.cmi \
    checker/cic.cmi
checker/modops.cmo : lib/util.cmi checker/univ.cmi lib/pp.cmi \
    checker/names.cmi checker/environ.cmi checker/declarations.cmi \
    checker/cic.cmi lib/cErrors.cmi checker/modops.cmi
checker/modops.cmx : lib/util.cmx checker/univ.cmx lib/pp.cmx \
    checker/names.cmx checker/environ.cmx checker/declarations.cmx \
    checker/cic.cmi lib/cErrors.cmx checker/modops.cmi
checker/modops.cmi : checker/names.cmi checker/environ.cmi checker/cic.cmi
checker/names.cmo : lib/util.cmi clib/unicode.cmi clib/predicate.cmi \
    lib/pp.cmi clib/option.cmi clib/int.cmi clib/hashset.cmi \
    clib/hashcons.cmi clib/hMap.cmi clib/cMap.cmi lib/cErrors.cmi \
    lib/cAst.cmi checker/names.cmi
checker/names.cmx : lib/util.cmx clib/unicode.cmx clib/predicate.cmx \
    lib/pp.cmx clib/option.cmx clib/int.cmx clib/hashset.cmx \
    clib/hashcons.cmx clib/hMap.cmx clib/cMap.cmx lib/cErrors.cmx \
    lib/cAst.cmx checker/names.cmi
checker/names.cmo : lib/util.cmi clib/unicode.cmi clib/predicate.cmi \
    lib/pp.cmi clib/option.cmi clib/int.cmi clib/hashset.cmi \
    clib/hashcons.cmi clib/hMap.cmi clib/cMap.cmi lib/cErrors.cmi \
    lib/cAst.cmi checker/names.cmi
checker/names.cmx : lib/util.cmx clib/unicode.cmx clib/predicate.cmx \
    lib/pp.cmx clib/option.cmx clib/int.cmx clib/hashset.cmx \
    clib/hashcons.cmx clib/hMap.cmx clib/cMap.cmx lib/cErrors.cmx \
    lib/cAst.cmx checker/names.cmi
checker/names.cmi : lib/util.cmi clib/predicate.cmi lib/pp.cmi clib/int.cmi \
    clib/cSig.cmi lib/cAst.cmi
checker/names.cmi : lib/util.cmi clib/predicate.cmi lib/pp.cmi clib/int.cmi \
    clib/cSig.cmi lib/cAst.cmi
checker/print.cmo : checker/univ.cmi lib/pp.cmi checker/names.cmi \
    checker/cic.cmi checker/print.cmi
checker/print.cmx : checker/univ.cmx lib/pp.cmx checker/names.cmx \
    checker/cic.cmi checker/print.cmi
checker/print.cmi : checker/cic.cmi
checker/reduction.cmo : lib/util.cmi checker/univ.cmi checker/term.cmi \
    lib/pp.cmi checker/names.cmi clib/int.cmi lib/flags.cmi \
    checker/esubst.cmi checker/environ.cmi lib/control.cmi \
    checker/closure.cmi checker/cic.cmi lib/cErrors.cmi checker/reduction.cmi
checker/reduction.cmx : lib/util.cmx checker/univ.cmx checker/term.cmx \
    lib/pp.cmx checker/names.cmx clib/int.cmx lib/flags.cmx \
    checker/esubst.cmx checker/environ.cmx lib/control.cmx \
    checker/closure.cmx checker/cic.cmi lib/cErrors.cmx checker/reduction.cmi
checker/reduction.cmi : checker/term.cmi checker/environ.cmi checker/cic.cmi
checker/safe_typing.cmo : lib/util.cmi lib/pp.cmi checker/names.cmi \
    checker/modops.cmi checker/mod_checking.cmi lib/flags.cmi \
    lib/feedback.cmi checker/environ.cmi checker/cic.cmi lib/cErrors.cmi \
    checker/safe_typing.cmi
checker/safe_typing.cmx : lib/util.cmx lib/pp.cmx checker/names.cmx \
    checker/modops.cmx checker/mod_checking.cmx lib/flags.cmx \
    lib/feedback.cmx checker/environ.cmx checker/cic.cmi lib/cErrors.cmx \
    checker/safe_typing.cmi
checker/safe_typing.cmi : checker/univ.cmi checker/environ.cmi \
    checker/cic.cmi clib/cUnix.cmi
checker/subtyping.cmo : lib/util.cmi checker/univ.cmi checker/reduction.cmi \
    lib/pp.cmi checker/names.cmi checker/modops.cmi clib/int.cmi \
    checker/inductive.cmi checker/environ.cmi checker/declarations.cmi \
    checker/cic.cmi lib/cErrors.cmi checker/subtyping.cmi
checker/subtyping.cmx : lib/util.cmx checker/univ.cmx checker/reduction.cmx \
    lib/pp.cmx checker/names.cmx checker/modops.cmx clib/int.cmx \
    checker/inductive.cmx checker/environ.cmx checker/declarations.cmx \
    checker/cic.cmi lib/cErrors.cmx checker/subtyping.cmi
checker/subtyping.cmi : checker/environ.cmi checker/cic.cmi
checker/term.cmo : lib/util.cmi checker/univ.cmi lib/pp.cmi \
    checker/names.cmi clib/int.cmi checker/esubst.cmi checker/cic.cmi \
    lib/cErrors.cmi checker/term.cmi
checker/term.cmx : lib/util.cmx checker/univ.cmx lib/pp.cmx \
    checker/names.cmx clib/int.cmx checker/esubst.cmx checker/cic.cmi \
    lib/cErrors.cmx checker/term.cmi
checker/term.cmi : checker/univ.cmi checker/names.cmi checker/esubst.cmi \
    checker/cic.cmi
checker/type_errors.cmo : checker/univ.cmi checker/names.cmi \
    checker/environ.cmi checker/cic.cmi checker/type_errors.cmi
checker/type_errors.cmx : checker/univ.cmx checker/names.cmx \
    checker/environ.cmx checker/cic.cmi checker/type_errors.cmi
checker/type_errors.cmi : checker/univ.cmi checker/names.cmi \
    checker/environ.cmi checker/cic.cmi
checker/typeops.cmo : lib/util.cmi checker/univ.cmi checker/type_errors.cmi \
    checker/term.cmi checker/reduction.cmi lib/pp.cmi checker/names.cmi \
    checker/inductive.cmi checker/environ.cmi checker/cic.cmi lib/cErrors.cmi \
    checker/typeops.cmi
checker/typeops.cmx : lib/util.cmx checker/univ.cmx checker/type_errors.cmx \
    checker/term.cmx checker/reduction.cmx lib/pp.cmx checker/names.cmx \
    checker/inductive.cmx checker/environ.cmx checker/cic.cmi lib/cErrors.cmx \
    checker/typeops.cmi
checker/typeops.cmi : checker/environ.cmi checker/cic.cmi
checker/univ.cmo : lib/util.cmi lib/pp.cmi checker/names.cmi clib/int.cmi \
    clib/hashset.cmi clib/hMap.cmi clib/cList.cmi lib/cErrors.cmi \
    clib/cArray.cmi checker/univ.cmi
checker/univ.cmx : lib/util.cmx lib/pp.cmx checker/names.cmx clib/int.cmx \
    clib/hashset.cmx clib/hMap.cmx clib/cList.cmx lib/cErrors.cmx \
    clib/cArray.cmx checker/univ.cmi
checker/univ.cmi : lib/pp.cmi checker/names.cmi clib/cSig.cmi
checker/validate.cmo : checker/values.cmi checker/validate.cmi
checker/validate.cmx : checker/values.cmx checker/validate.cmi
checker/validate.cmi : checker/values.cmi
checker/values.cmo : checker/values.cmi
checker/values.cmx : checker/values.cmi
checker/values.cmi :
checker/votour.cmo : checker/values.cmi clib/cObj.cmi checker/analyze.cmi \
    checker/votour.cmi
checker/votour.cmx : checker/values.cmx clib/cObj.cmx checker/analyze.cmx \
    checker/votour.cmi
checker/votour.cmi :
dev/checker_printers.cmo : checker/univ.cmi lib/pp.cmi checker/names.cmi \
    lib/loc.cmi clib/int.cmi lib/future.cmi clib/bigint.cmi \
    dev/checker_printers.cmi
dev/checker_printers.cmx : checker/univ.cmx lib/pp.cmx checker/names.cmx \
    lib/loc.cmx clib/int.cmx lib/future.cmx clib/bigint.cmx \
    dev/checker_printers.cmi
dev/checker_printers.cmi : checker/univ.cmi lib/pp.cmi checker/names.cmi \
    lib/loc.cmi clib/int.cmi lib/future.cmi clib/bigint.cmi

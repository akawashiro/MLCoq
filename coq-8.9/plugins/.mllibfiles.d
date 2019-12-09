plugins/ssrmatching/ssrmatching_plugin_MLPACK_DEPENDENCIES:=plugins/ssrmatching/ssrmatching plugins/ssrmatching/g_ssrmatching
plugins/ssrmatching/ssrmatching_FORPACK:= -for-pack Ssrmatching_plugin
plugins/ssrmatching/g_ssrmatching_FORPACK:= -for-pack Ssrmatching_plugin
plugins/ssrmatching/ssrmatching_plugin.cmo:$(addsuffix .cmo,$(plugins/ssrmatching/ssrmatching_plugin_MLPACK_DEPENDENCIES))
plugins/ssrmatching/ssrmatching_plugin.cmx:$(addsuffix .cmx,$(plugins/ssrmatching/ssrmatching_plugin_MLPACK_DEPENDENCIES))
plugins/setoid_ring/newring_plugin_MLPACK_DEPENDENCIES:=plugins/setoid_ring/newring_ast plugins/setoid_ring/newring plugins/setoid_ring/g_newring
plugins/setoid_ring/newring_ast_FORPACK:= -for-pack Newring_plugin
plugins/setoid_ring/newring_FORPACK:= -for-pack Newring_plugin
plugins/setoid_ring/g_newring_FORPACK:= -for-pack Newring_plugin
plugins/setoid_ring/newring_plugin.cmo:$(addsuffix .cmo,$(plugins/setoid_ring/newring_plugin_MLPACK_DEPENDENCIES))
plugins/setoid_ring/newring_plugin.cmx:$(addsuffix .cmx,$(plugins/setoid_ring/newring_plugin_MLPACK_DEPENDENCIES))
plugins/quote/quote_plugin_MLPACK_DEPENDENCIES:=plugins/quote/quote plugins/quote/g_quote
plugins/quote/quote_FORPACK:= -for-pack Quote_plugin
plugins/quote/g_quote_FORPACK:= -for-pack Quote_plugin
plugins/quote/quote_plugin.cmo:$(addsuffix .cmo,$(plugins/quote/quote_plugin_MLPACK_DEPENDENCIES))
plugins/quote/quote_plugin.cmx:$(addsuffix .cmx,$(plugins/quote/quote_plugin_MLPACK_DEPENDENCIES))
plugins/funind/recdef_plugin_MLPACK_DEPENDENCIES:=plugins/funind/indfun_common plugins/funind/glob_termops plugins/funind/recdef plugins/funind/glob_term_to_relation plugins/funind/functional_principles_proofs plugins/funind/functional_principles_types plugins/funind/invfun plugins/funind/indfun plugins/funind/g_indfun
plugins/funind/indfun_common_FORPACK:= -for-pack Recdef_plugin
plugins/funind/glob_termops_FORPACK:= -for-pack Recdef_plugin
plugins/funind/recdef_FORPACK:= -for-pack Recdef_plugin
plugins/funind/glob_term_to_relation_FORPACK:= -for-pack Recdef_plugin
plugins/funind/functional_principles_proofs_FORPACK:= -for-pack Recdef_plugin
plugins/funind/functional_principles_types_FORPACK:= -for-pack Recdef_plugin
plugins/funind/invfun_FORPACK:= -for-pack Recdef_plugin
plugins/funind/indfun_FORPACK:= -for-pack Recdef_plugin
plugins/funind/g_indfun_FORPACK:= -for-pack Recdef_plugin
plugins/funind/recdef_plugin.cmo:$(addsuffix .cmo,$(plugins/funind/recdef_plugin_MLPACK_DEPENDENCIES))
plugins/funind/recdef_plugin.cmx:$(addsuffix .cmx,$(plugins/funind/recdef_plugin_MLPACK_DEPENDENCIES))
plugins/micromega/micromega_plugin_MLPACK_DEPENDENCIES:=plugins/micromega/sos_types plugins/micromega/micromega plugins/micromega/mutils plugins/micromega/polynomial plugins/micromega/mfourier plugins/micromega/certificate plugins/micromega/persistent_cache plugins/micromega/coq_micromega plugins/micromega/g_micromega
plugins/micromega/sos_types_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/micromega_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/mutils_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/polynomial_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/mfourier_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/certificate_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/persistent_cache_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/coq_micromega_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/g_micromega_FORPACK:= -for-pack Micromega_plugin
plugins/micromega/micromega_plugin.cmo:$(addsuffix .cmo,$(plugins/micromega/micromega_plugin_MLPACK_DEPENDENCIES))
plugins/micromega/micromega_plugin.cmx:$(addsuffix .cmx,$(plugins/micromega/micromega_plugin_MLPACK_DEPENDENCIES))
plugins/romega/romega_plugin_MLPACK_DEPENDENCIES:=plugins/romega/const_omega plugins/romega/refl_omega plugins/romega/g_romega
plugins/romega/const_omega_FORPACK:= -for-pack Romega_plugin
plugins/romega/refl_omega_FORPACK:= -for-pack Romega_plugin
plugins/romega/g_romega_FORPACK:= -for-pack Romega_plugin
plugins/romega/romega_plugin.cmo:$(addsuffix .cmo,$(plugins/romega/romega_plugin_MLPACK_DEPENDENCIES))
plugins/romega/romega_plugin.cmx:$(addsuffix .cmx,$(plugins/romega/romega_plugin_MLPACK_DEPENDENCIES))
plugins/rtauto/rtauto_plugin_MLPACK_DEPENDENCIES:=plugins/rtauto/proof_search plugins/rtauto/refl_tauto plugins/rtauto/g_rtauto
plugins/rtauto/proof_search_FORPACK:= -for-pack Rtauto_plugin
plugins/rtauto/refl_tauto_FORPACK:= -for-pack Rtauto_plugin
plugins/rtauto/g_rtauto_FORPACK:= -for-pack Rtauto_plugin
plugins/rtauto/rtauto_plugin.cmo:$(addsuffix .cmo,$(plugins/rtauto/rtauto_plugin_MLPACK_DEPENDENCIES))
plugins/rtauto/rtauto_plugin.cmx:$(addsuffix .cmx,$(plugins/rtauto/rtauto_plugin_MLPACK_DEPENDENCIES))
plugins/ssr/ssreflect_plugin_MLPACK_DEPENDENCIES:=plugins/ssr/ssrprinters plugins/ssr/ssrcommon plugins/ssr/ssrtacticals plugins/ssr/ssrelim plugins/ssr/ssrview plugins/ssr/ssrbwd plugins/ssr/ssrequality plugins/ssr/ssripats plugins/ssr/ssrfwd plugins/ssr/ssrparser plugins/ssr/ssrvernac
plugins/ssr/ssrprinters_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrcommon_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrtacticals_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrelim_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrview_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrbwd_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrequality_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssripats_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrfwd_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrparser_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssrvernac_FORPACK:= -for-pack Ssreflect_plugin
plugins/ssr/ssreflect_plugin.cmo:$(addsuffix .cmo,$(plugins/ssr/ssreflect_plugin_MLPACK_DEPENDENCIES))
plugins/ssr/ssreflect_plugin.cmx:$(addsuffix .cmx,$(plugins/ssr/ssreflect_plugin_MLPACK_DEPENDENCIES))
plugins/derive/derive_plugin_MLPACK_DEPENDENCIES:=plugins/derive/derive plugins/derive/g_derive
plugins/derive/derive_FORPACK:= -for-pack Derive_plugin
plugins/derive/g_derive_FORPACK:= -for-pack Derive_plugin
plugins/derive/derive_plugin.cmo:$(addsuffix .cmo,$(plugins/derive/derive_plugin_MLPACK_DEPENDENCIES))
plugins/derive/derive_plugin.cmx:$(addsuffix .cmx,$(plugins/derive/derive_plugin_MLPACK_DEPENDENCIES))
plugins/cc/cc_plugin_MLPACK_DEPENDENCIES:=plugins/cc/ccalgo plugins/cc/ccproof plugins/cc/cctac plugins/cc/g_congruence
plugins/cc/ccalgo_FORPACK:= -for-pack Cc_plugin
plugins/cc/ccproof_FORPACK:= -for-pack Cc_plugin
plugins/cc/cctac_FORPACK:= -for-pack Cc_plugin
plugins/cc/g_congruence_FORPACK:= -for-pack Cc_plugin
plugins/cc/cc_plugin.cmo:$(addsuffix .cmo,$(plugins/cc/cc_plugin_MLPACK_DEPENDENCIES))
plugins/cc/cc_plugin.cmx:$(addsuffix .cmx,$(plugins/cc/cc_plugin_MLPACK_DEPENDENCIES))
plugins/omega/omega_plugin_MLPACK_DEPENDENCIES:=plugins/omega/omega plugins/omega/coq_omega plugins/omega/g_omega
plugins/omega/omega_FORPACK:= -for-pack Omega_plugin
plugins/omega/coq_omega_FORPACK:= -for-pack Omega_plugin
plugins/omega/g_omega_FORPACK:= -for-pack Omega_plugin
plugins/omega/omega_plugin.cmo:$(addsuffix .cmo,$(plugins/omega/omega_plugin_MLPACK_DEPENDENCIES))
plugins/omega/omega_plugin.cmx:$(addsuffix .cmx,$(plugins/omega/omega_plugin_MLPACK_DEPENDENCIES))
plugins/nsatz/nsatz_plugin_MLPACK_DEPENDENCIES:=plugins/nsatz/utile plugins/nsatz/polynom plugins/nsatz/ideal plugins/nsatz/nsatz plugins/nsatz/g_nsatz
plugins/nsatz/utile_FORPACK:= -for-pack Nsatz_plugin
plugins/nsatz/polynom_FORPACK:= -for-pack Nsatz_plugin
plugins/nsatz/ideal_FORPACK:= -for-pack Nsatz_plugin
plugins/nsatz/nsatz_FORPACK:= -for-pack Nsatz_plugin
plugins/nsatz/g_nsatz_FORPACK:= -for-pack Nsatz_plugin
plugins/nsatz/nsatz_plugin.cmo:$(addsuffix .cmo,$(plugins/nsatz/nsatz_plugin_MLPACK_DEPENDENCIES))
plugins/nsatz/nsatz_plugin.cmx:$(addsuffix .cmx,$(plugins/nsatz/nsatz_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/ascii_syntax_plugin_MLPACK_DEPENDENCIES:=plugins/syntax/ascii_syntax
plugins/syntax/ascii_syntax_FORPACK:= -for-pack Ascii_syntax_plugin
plugins/syntax/ascii_syntax_plugin.cmo:$(addsuffix .cmo,$(plugins/syntax/ascii_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/ascii_syntax_plugin.cmx:$(addsuffix .cmx,$(plugins/syntax/ascii_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/numeral_notation_plugin_MLPACK_DEPENDENCIES:=plugins/syntax/numeral plugins/syntax/g_numeral
plugins/syntax/numeral_FORPACK:= -for-pack Numeral_notation_plugin
plugins/syntax/g_numeral_FORPACK:= -for-pack Numeral_notation_plugin
plugins/syntax/numeral_notation_plugin.cmo:$(addsuffix .cmo,$(plugins/syntax/numeral_notation_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/numeral_notation_plugin.cmx:$(addsuffix .cmx,$(plugins/syntax/numeral_notation_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/r_syntax_plugin_MLPACK_DEPENDENCIES:=plugins/syntax/r_syntax
plugins/syntax/r_syntax_FORPACK:= -for-pack R_syntax_plugin
plugins/syntax/r_syntax_plugin.cmo:$(addsuffix .cmo,$(plugins/syntax/r_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/r_syntax_plugin.cmx:$(addsuffix .cmx,$(plugins/syntax/r_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/string_syntax_plugin_MLPACK_DEPENDENCIES:=plugins/syntax/string_syntax
plugins/syntax/string_syntax_FORPACK:= -for-pack String_syntax_plugin
plugins/syntax/string_syntax_plugin.cmo:$(addsuffix .cmo,$(plugins/syntax/string_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/string_syntax_plugin.cmx:$(addsuffix .cmx,$(plugins/syntax/string_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/int31_syntax_plugin_MLPACK_DEPENDENCIES:=plugins/syntax/int31_syntax
plugins/syntax/int31_syntax_FORPACK:= -for-pack Int31_syntax_plugin
plugins/syntax/int31_syntax_plugin.cmo:$(addsuffix .cmo,$(plugins/syntax/int31_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/syntax/int31_syntax_plugin.cmx:$(addsuffix .cmx,$(plugins/syntax/int31_syntax_plugin_MLPACK_DEPENDENCIES))
plugins/btauto/btauto_plugin_MLPACK_DEPENDENCIES:=plugins/btauto/refl_btauto plugins/btauto/g_btauto
plugins/btauto/refl_btauto_FORPACK:= -for-pack Btauto_plugin
plugins/btauto/g_btauto_FORPACK:= -for-pack Btauto_plugin
plugins/btauto/btauto_plugin.cmo:$(addsuffix .cmo,$(plugins/btauto/btauto_plugin_MLPACK_DEPENDENCIES))
plugins/btauto/btauto_plugin.cmx:$(addsuffix .cmx,$(plugins/btauto/btauto_plugin_MLPACK_DEPENDENCIES))
plugins/extraction/extraction_plugin_MLPACK_DEPENDENCIES:=plugins/extraction/miniml plugins/extraction/table plugins/extraction/mlutil plugins/extraction/modutil plugins/extraction/extraction plugins/extraction/common plugins/extraction/ocaml plugins/extraction/haskell plugins/extraction/scheme plugins/extraction/json plugins/extraction/extract_env plugins/extraction/g_extraction
plugins/extraction/miniml_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/table_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/mlutil_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/modutil_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/extraction_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/common_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/ocaml_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/haskell_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/scheme_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/json_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/extract_env_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/g_extraction_FORPACK:= -for-pack Extraction_plugin
plugins/extraction/extraction_plugin.cmo:$(addsuffix .cmo,$(plugins/extraction/extraction_plugin_MLPACK_DEPENDENCIES))
plugins/extraction/extraction_plugin.cmx:$(addsuffix .cmx,$(plugins/extraction/extraction_plugin_MLPACK_DEPENDENCIES))
plugins/ltac/ltac_plugin_MLPACK_DEPENDENCIES:=plugins/ltac/tacexpr plugins/ltac/tacarg plugins/ltac/tacsubst plugins/ltac/tacenv plugins/ltac/pptactic plugins/ltac/pltac plugins/ltac/taccoerce plugins/ltac/tactic_debug plugins/ltac/tacintern plugins/ltac/tacentries plugins/ltac/profile_ltac plugins/ltac/tactic_matching plugins/ltac/tacinterp plugins/ltac/evar_tactics plugins/ltac/tactic_option plugins/ltac/extraargs plugins/ltac/g_obligations plugins/ltac/coretactics plugins/ltac/extratactics plugins/ltac/profile_ltac_tactics plugins/ltac/g_auto plugins/ltac/g_class plugins/ltac/rewrite plugins/ltac/g_rewrite plugins/ltac/g_eqdecide plugins/ltac/g_tactic plugins/ltac/g_ltac
plugins/ltac/tacexpr_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tacarg_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tacsubst_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tacenv_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/pptactic_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/pltac_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/taccoerce_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tactic_debug_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tacintern_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tacentries_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/profile_ltac_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tactic_matching_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tacinterp_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/evar_tactics_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/tactic_option_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/extraargs_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/g_obligations_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/coretactics_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/extratactics_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/profile_ltac_tactics_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/g_auto_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/g_class_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/rewrite_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/g_rewrite_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/g_eqdecide_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/g_tactic_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/g_ltac_FORPACK:= -for-pack Ltac_plugin
plugins/ltac/ltac_plugin.cmo:$(addsuffix .cmo,$(plugins/ltac/ltac_plugin_MLPACK_DEPENDENCIES))
plugins/ltac/ltac_plugin.cmx:$(addsuffix .cmx,$(plugins/ltac/ltac_plugin_MLPACK_DEPENDENCIES))
plugins/ltac/tauto_plugin_MLPACK_DEPENDENCIES:=plugins/ltac/tauto
plugins/ltac/tauto_FORPACK:= -for-pack Tauto_plugin
plugins/ltac/tauto_plugin.cmo:$(addsuffix .cmo,$(plugins/ltac/tauto_plugin_MLPACK_DEPENDENCIES))
plugins/ltac/tauto_plugin.cmx:$(addsuffix .cmx,$(plugins/ltac/tauto_plugin_MLPACK_DEPENDENCIES))
plugins/firstorder/ground_plugin_MLPACK_DEPENDENCIES:=plugins/firstorder/formula plugins/firstorder/unify plugins/firstorder/sequent plugins/firstorder/rules plugins/firstorder/instances plugins/firstorder/ground plugins/firstorder/g_ground
plugins/firstorder/formula_FORPACK:= -for-pack Ground_plugin
plugins/firstorder/unify_FORPACK:= -for-pack Ground_plugin
plugins/firstorder/sequent_FORPACK:= -for-pack Ground_plugin
plugins/firstorder/rules_FORPACK:= -for-pack Ground_plugin
plugins/firstorder/instances_FORPACK:= -for-pack Ground_plugin
plugins/firstorder/ground_FORPACK:= -for-pack Ground_plugin
plugins/firstorder/g_ground_FORPACK:= -for-pack Ground_plugin
plugins/firstorder/ground_plugin.cmo:$(addsuffix .cmo,$(plugins/firstorder/ground_plugin_MLPACK_DEPENDENCIES))
plugins/firstorder/ground_plugin.cmx:$(addsuffix .cmx,$(plugins/firstorder/ground_plugin_MLPACK_DEPENDENCIES))

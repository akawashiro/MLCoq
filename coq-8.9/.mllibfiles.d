ide/ide_common_MLLIB_DEPENDENCIES:=ide/protocol/xml_lexer ide/protocol/xml_parser ide/protocol/xml_printer ide/protocol/serialize ide/protocol/richpp ide/protocol/xmlprotocol ide/document
ide/ide_common.cma:$(addsuffix .cmo,$(ide/ide_common_MLLIB_DEPENDENCIES))
ide/ide_common.cmxa:$(addsuffix .cmx,$(ide/ide_common_MLLIB_DEPENDENCIES))
ide/protocol/ideprotocol_MLLIB_DEPENDENCIES:=ide/protocol/xml_lexer ide/protocol/xml_parser ide/protocol/xml_printer ide/protocol/serialize ide/protocol/richpp ide/protocol/interface ide/protocol/xmlprotocol
ide/protocol/ideprotocol.cma:$(addsuffix .cmo,$(ide/protocol/ideprotocol_MLLIB_DEPENDENCIES))
ide/protocol/ideprotocol.cmxa:$(addsuffix .cmx,$(ide/protocol/ideprotocol_MLLIB_DEPENDENCIES))
ide/ide_MLLIB_DEPENDENCIES:=ide/minilib ide/configwin_messages ide/configwin_ihm ide/configwin ide/tags ide/wg_Notebook ide/config_lexer ide/utf8_convert ide/preferences vernac/topfmt ide/ideutils ide/coq ide/coq_lex ide/sentence ide/gtk_parsing ide/wg_Segment ide/wg_ProofView ide/wg_MessageView ide/wg_RoutedMessageViews ide/wg_Detachable ide/wg_Find ide/wg_Completion ide/wg_ScriptView ide/coq_commands ide/fileOps ide/document ide/coqOps ide/wg_Command ide/session ide/coqide_ui ide/nanoPG ide/coqide
ide/ide.cma:$(addsuffix .cmo,$(ide/ide_MLLIB_DEPENDENCIES))
ide/ide.cmxa:$(addsuffix .cmx,$(ide/ide_MLLIB_DEPENDENCIES))
vernac/vernac_MLLIB_DEPENDENCIES:=vernac/vernacexpr vernac/pvernac vernac/g_vernac vernac/g_proofs vernac/vernacprop vernac/himsg vernac/explainErr vernac/locality vernac/egramml vernac/vernacinterp vernac/ppvernac vernac/proof_using vernac/lemmas vernac/class vernac/egramcoq vernac/metasyntax vernac/auto_ind_decl vernac/search vernac/indschemes vernac/declareDef vernac/obligations vernac/comDefinition vernac/comAssumption vernac/comInductive vernac/comFixpoint vernac/comProgramFixpoint vernac/classes vernac/record vernac/assumptions vernac/vernacstate vernac/mltop vernac/topfmt vernac/vernacentries vernac/misctypes
vernac/vernac.cma:$(addsuffix .cmo,$(vernac/vernac_MLLIB_DEPENDENCIES))
vernac/vernac.cmxa:$(addsuffix .cmx,$(vernac/vernac_MLLIB_DEPENDENCIES))
pretyping/pretyping_MLLIB_DEPENDENCIES:=pretyping/geninterp pretyping/locus pretyping/locusops pretyping/pretype_errors pretyping/reductionops pretyping/inductiveops pretyping/inferCumulativity pretyping/vnorm pretyping/arguments_renaming pretyping/nativenorm pretyping/retyping pretyping/cbv pretyping/find_subterm pretyping/evardefine pretyping/evarsolve pretyping/recordops pretyping/heads pretyping/evarconv pretyping/typing pretyping/glob_term pretyping/ltac_pretype pretyping/glob_ops pretyping/pattern pretyping/patternops pretyping/constr_matching pretyping/tacred pretyping/typeclasses_errors pretyping/typeclasses pretyping/classops pretyping/program pretyping/coercion pretyping/detyping pretyping/indrec pretyping/cases pretyping/pretyping pretyping/unification
pretyping/pretyping.cma:$(addsuffix .cmo,$(pretyping/pretyping_MLLIB_DEPENDENCIES))
pretyping/pretyping.cmxa:$(addsuffix .cmx,$(pretyping/pretyping_MLLIB_DEPENDENCIES))
clib/clib_MLLIB_DEPENDENCIES:=clib/cObj clib/cEphemeron clib/hashset clib/hashcons clib/orderedType clib/cSet clib/cMap clib/cList clib/cString clib/cStack clib/int clib/range clib/hMap clib/bigint clib/cArray clib/option clib/cUnix clib/segmenttree clib/unicodetable clib/unicode clib/minisys clib/cThread clib/trie clib/predicate clib/heap clib/unionfind clib/dyn clib/store clib/exninfo clib/backtrace clib/iStream clib/terminal clib/monad clib/diff2
clib/clib.cma:$(addsuffix .cmo,$(clib/clib_MLLIB_DEPENDENCIES))
clib/clib.cmxa:$(addsuffix .cmx,$(clib/clib_MLLIB_DEPENDENCIES))
tactics/tactics_MLLIB_DEPENDENCIES:=tactics/dnet tactics/dn tactics/btermdn tactics/tacticals tactics/hipattern tactics/ind_tables tactics/eqschemes tactics/elimschemes tactics/tactics tactics/elim tactics/equality tactics/contradiction tactics/inv tactics/leminv tactics/hints tactics/auto tactics/eauto tactics/class_tactics tactics/term_dnet tactics/eqdecide tactics/autorewrite
tactics/tactics.cma:$(addsuffix .cmo,$(tactics/tactics_MLLIB_DEPENDENCIES))
tactics/tactics.cmxa:$(addsuffix .cmx,$(tactics/tactics_MLLIB_DEPENDENCIES))
interp/interp_MLLIB_DEPENDENCIES:=interp/constrexpr interp/genredexpr interp/redops proofs/tactypes interp/stdarg interp/genintern interp/notation_term interp/notation_ops interp/notation interp/syntax_def interp/smartlocate interp/constrexpr_ops interp/dumpglob interp/reserve interp/impargs interp/implicit_quantifiers interp/constrintern interp/modintern interp/constrextern interp/discharge interp/declare
interp/interp.cma:$(addsuffix .cmo,$(interp/interp_MLLIB_DEPENDENCIES))
interp/interp.cmxa:$(addsuffix .cmx,$(interp/interp_MLLIB_DEPENDENCIES))
proofs/proofs_MLLIB_DEPENDENCIES:=proofs/miscprint proofs/goal proofs/evar_refiner proofs/proof_type proofs/logic proofs/refine proofs/proof proofs/goal_select proofs/proof_bullet proofs/proof_global proofs/redexpr proofs/refiner proofs/tacmach proofs/pfedit proofs/clenv proofs/clenvtac
proofs/proofs.cma:$(addsuffix .cmo,$(proofs/proofs_MLLIB_DEPENDENCIES))
proofs/proofs.cmxa:$(addsuffix .cmx,$(proofs/proofs_MLLIB_DEPENDENCIES))
printing/printing_MLLIB_DEPENDENCIES:=printing/genprint printing/pputils printing/ppconstr printing/proof_diffs printing/printer printing/printmod printing/prettyp
printing/printing.cma:$(addsuffix .cmo,$(printing/printing_MLLIB_DEPENDENCIES))
printing/printing.cmxa:$(addsuffix .cmx,$(printing/printing_MLLIB_DEPENDENCIES))
library/library_MLLIB_DEPENDENCIES:=library/libnames library/globnames library/libobject library/summary library/nametab library/global library/decl_kinds library/lib library/declaremods library/loadpath library/library library/states library/kindops library/dischargedhypsmap library/goptions library/decls library/keys library/coqlib
library/library.cma:$(addsuffix .cmo,$(library/library_MLLIB_DEPENDENCIES))
library/library.cmxa:$(addsuffix .cmx,$(library/library_MLLIB_DEPENDENCIES))
stm/stm_MLLIB_DEPENDENCIES:=stm/spawned stm/dag stm/vcs stm/tQueue stm/workerPool stm/vernac_classifier stm/coqworkmgrApi stm/asyncTaskQueue stm/stm stm/proofBlockDelimiter stm/vio_checking
stm/stm.cma:$(addsuffix .cmo,$(stm/stm_MLLIB_DEPENDENCIES))
stm/stm.cmxa:$(addsuffix .cmx,$(stm/stm_MLLIB_DEPENDENCIES))
toplevel/toplevel_MLLIB_DEPENDENCIES:=toplevel/vernac toplevel/usage toplevel/coqinit toplevel/coqargs toplevel/g_toplevel toplevel/coqloop toplevel/coqtop toplevel/workerLoop
toplevel/toplevel.cma:$(addsuffix .cmo,$(toplevel/toplevel_MLLIB_DEPENDENCIES))
toplevel/toplevel.cmxa:$(addsuffix .cmx,$(toplevel/toplevel_MLLIB_DEPENDENCIES))
lib/lib_MLLIB_DEPENDENCIES:=config/coq_config lib/hook lib/flags lib/control lib/util lib/pp lib/pp_diff lib/stateid lib/loc lib/feedback lib/cErrors lib/cWarnings lib/rtree lib/system lib/explore lib/cProfile lib/future lib/spawn lib/cAst lib/dAst lib/genarg lib/remoteCounter lib/aux_file lib/envars lib/coqProject_file
lib/lib.cma:$(addsuffix .cmo,$(lib/lib_MLLIB_DEPENDENCIES))
lib/lib.cmxa:$(addsuffix .cmx,$(lib/lib_MLLIB_DEPENDENCIES))
parsing/parsing_MLLIB_DEPENDENCIES:=parsing/tok parsing/cLexer parsing/extend parsing/notation_gram parsing/ppextend parsing/notgram_ops parsing/pcoq parsing/g_constr parsing/g_prim
parsing/parsing.cma:$(addsuffix .cmo,$(parsing/parsing_MLLIB_DEPENDENCIES))
parsing/parsing.cmxa:$(addsuffix .cmx,$(parsing/parsing_MLLIB_DEPENDENCIES))
engine/engine_MLLIB_DEPENDENCIES:=engine/univNames engine/univGen engine/univSubst engine/univProblem engine/univMinim engine/universes engine/univops engine/uState engine/nameops engine/evar_kinds engine/evd engine/eConstr engine/namegen engine/termops engine/evarutil engine/logic_monad engine/proofview_monad engine/proofview engine/ftactic
engine/engine.cma:$(addsuffix .cmo,$(engine/engine_MLLIB_DEPENDENCIES))
engine/engine.cmxa:$(addsuffix .cmx,$(engine/engine_MLLIB_DEPENDENCIES))
kernel/kernel_MLLIB_DEPENDENCIES:=kernel/names kernel/uint31 kernel/univ kernel/uGraph kernel/esubst kernel/sorts kernel/evar kernel/context kernel/constr kernel/vars kernel/term kernel/mod_subst kernel/vmvalues kernel/cbytecodes kernel/copcodes kernel/cemitcodes kernel/opaqueproof kernel/declarations kernel/entries kernel/nativevalues kernel/cPrimitives kernel/declareops kernel/retroknowledge kernel/conv_oracle kernel/environ kernel/cClosure kernel/reduction kernel/clambda kernel/nativelambda kernel/cbytegen kernel/nativecode kernel/nativelib kernel/csymtable kernel/vm kernel/vconv kernel/nativeconv kernel/type_errors kernel/modops kernel/inductive kernel/typeops kernel/indtypes kernel/cooking kernel/term_typing kernel/subtyping kernel/mod_typing kernel/nativelibrary kernel/safe_typing
kernel/kernel.cma:$(addsuffix .cmo,$(kernel/kernel_MLLIB_DEPENDENCIES))
kernel/kernel.cmxa:$(addsuffix .cmx,$(kernel/kernel_MLLIB_DEPENDENCIES))

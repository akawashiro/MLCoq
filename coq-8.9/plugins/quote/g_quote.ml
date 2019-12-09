

open Ltac_plugin
open Names
open Tacexpr
open Geninterp
open Quote
open Stdarg
open Tacarg


let __coq_plugin_name = "quote_plugin"
let _ = Mltop.add_known_module __coq_plugin_name


let cont = Id.of_string "cont"
let x = Id.of_string "x"

let make_cont (k : Val.t) (c : EConstr.t) =
  let c = Tacinterp.Value.of_constr c in
  let tac = TacCall (Loc.tag (Locus.ArgVar CAst.(make cont), [Reference (Locus.ArgVar CAst.(make x))])) in
  let ist = { lfun = Id.Map.add cont k (Id.Map.singleton x c); extra = TacStore.empty; } in
  Tacinterp.eval_tactic_ist ist (TacArg (Loc.tag tac))


let () = Tacentries.tactic_extend __coq_plugin_name "quote" ~level:0 Tacentries.([
         (TyML (TyIdent ("quote", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "f", 
                                  TyNil)), fun f ist  ->  quote f [] ));
         (TyML (TyIdent ("quote", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "f", 
                                  TyIdent ("[", TyArg (Extend.TUlist1 (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ident)), "lc", 
                                                TyIdent ("]", TyNil))))), 
          fun f lc ist  ->  quote f lc ));
         (TyML (TyIdent ("quote", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "f", 
                                  TyIdent ("in", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                                 TyIdent ("using", TyArg (
                                                                   Extend.TUentry (Genarg.get_arg_tag wit_tactic), "k", 
                                                                   TyNil)))))), 
          fun f c k ist  ->  gen_quote (make_cont k) c f [] ));
         (TyML (TyIdent ("quote", TyArg (Extend.TUentry (Genarg.get_arg_tag wit_ident), "f", 
                                  TyIdent ("[", TyArg (Extend.TUlist1 (
                                                       Extend.TUentry (Genarg.get_arg_tag wit_ident)), "lc", 
                                                TyIdent ("]", TyIdent ("in", 
                                                              TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_constr), "c", 
                                                              TyIdent ("using", 
                                                              TyArg (
                                                              Extend.TUentry (Genarg.get_arg_tag wit_tactic), "k", 
                                                              TyNil))))))))), 
          fun f lc c k ist  ->  gen_quote (make_cont k) c f lc ))
         ])


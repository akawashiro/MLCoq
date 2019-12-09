

open Pp
open CErrors
open Util
open Names
open Namegen
open Tacexpr
open Genredexpr
open Constrexpr
open Libnames
open Tok
open Tactypes
open Tactics
open Inv
open Locus
open Decl_kinds

open Pcoq


let all_with delta = Redops.make_red_flag [FBeta;FMatch;FFix;FCofix;FZeta;delta]

let tactic_kw = [ "->"; "<-" ; "by" ]
let _ = List.iter CLexer.add_keyword tactic_kw

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let test_lpar_id_coloneq =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "(" ->
            (match stream_nth 1 strm with
              | IDENT _ ->
                  (match stream_nth 2 strm with
	            | KEYWORD ":=" -> ()
	            | _ -> err ())
	      | _ -> err ())
	| _ -> err ())

(* Hack to recognize "(x)" *)
let test_lpar_id_rpar =
  Gram.Entry.of_parser "lpar_id_coloneq"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "(" ->
            (match stream_nth 1 strm with
              | IDENT _ ->
                  (match stream_nth 2 strm with
	            | KEYWORD ")" -> ()
	            | _ -> err ())
	      | _ -> err ())
	| _ -> err ())

(* idem for (x:=t) and (1:=t) *)
let test_lpar_idnum_coloneq =
  Gram.Entry.of_parser "test_lpar_idnum_coloneq"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "(" ->
            (match stream_nth 1 strm with
              | IDENT _ | INT _ ->
                  (match stream_nth 2 strm with
                    | KEYWORD ":=" -> ()
                    | _ -> err ())
              | _ -> err ())
        | _ -> err ())

(* idem for (x:t) *)
open Extraargs

(* idem for (x1..xn:t) [n^2 complexity but exceptional use] *)
let check_for_coloneq =
  Gram.Entry.of_parser "lpar_id_colon"
    (fun strm ->
      let rec skip_to_rpar p n =
	match List.last (Stream.npeek n strm) with
        | KEYWORD "(" -> skip_to_rpar (p+1) (n+1)
        | KEYWORD ")" -> if Int.equal p 0 then n+1 else skip_to_rpar (p-1) (n+1)
	| KEYWORD "." -> err ()
	| _ -> skip_to_rpar p (n+1) in
      let rec skip_names n =
	match List.last (Stream.npeek n strm) with
        | IDENT _ | KEYWORD "_" -> skip_names (n+1)
	| KEYWORD ":" -> skip_to_rpar 0 (n+1) (* skip a constr *)
	| _ -> err () in
      let rec skip_binders n =
	match List.last (Stream.npeek n strm) with
        | KEYWORD "(" -> skip_binders (skip_names (n+1))
        | IDENT _ | KEYWORD "_" -> skip_binders (n+1)
	| KEYWORD ":=" -> ()
	| _ -> err () in
      match stream_nth 0 strm with
      | KEYWORD "(" -> skip_binders 2
      | _ -> err ())

let lookup_at_as_comma =
  Gram.Entry.of_parser "lookup_at_as_comma"
    (fun strm ->
      match stream_nth 0 strm with
	| KEYWORD (","|"at"|"as") -> ()
	| _ -> err ())

open Constr
open Prim
open Pltac

let mk_fix_tac (loc,id,bl,ann,ty) =
  let n =
    match bl,ann with
        [([_],_,_)], None -> 1
      | _, Some x ->
          let ids = List.map (fun x -> x.CAst.v) (List.flatten (List.map (fun (nal,_,_) -> nal) bl)) in
          (try List.index Names.Name.equal x.CAst.v ids
          with Not_found -> user_err Pp.(str "No such fix variable."))
      | _ -> user_err Pp.(str "Cannot guess decreasing argument of fix.") in
  let bl = List.map (fun (nal,bk,t) -> CLocalAssum (nal,bk,t)) bl in
  (id,n, CAst.make ~loc @@ CProdN(bl,ty))

let mk_cofix_tac (loc,id,bl,ann,ty) =
  let _ = Option.map (fun { CAst.loc = aloc } ->
    user_err ?loc:aloc
      ~hdr:"Constr:mk_cofix_tac"
      (Pp.str"Annotation forbidden in cofix expression.")) ann in
  let bl = List.map (fun (nal,bk,t) -> CLocalAssum (nal,bk,t)) bl in
  (id,CAst.make ~loc @@ CProdN(bl,ty))

(* Functions overloaded by quotifier *)
let destruction_arg_of_constr (c,lbind as clbind) = match lbind with
  | NoBindings ->
    begin
      try ElimOnIdent (CAst.make ?loc:(Constrexpr_ops.constr_loc c) (Constrexpr_ops.coerce_to_id c).CAst.v)
      with e when CErrors.noncritical e -> ElimOnConstr clbind
    end
  | _ -> ElimOnConstr clbind

let mkNumeral n = Numeral (string_of_int (abs n), 0<=n)

let mkTacCase with_evar = function
  | [(clear,ElimOnConstr cl),(None,None),None],None ->
      TacCase (with_evar,(clear,cl))
  (* Reinterpret numbers as a notation for terms *)
  | [(clear,ElimOnAnonHyp n),(None,None),None],None ->
      TacCase (with_evar,
        (clear,(CAst.make @@ CPrim (mkNumeral n),
         NoBindings)))
  (* Reinterpret ident as notations for variables in the context *)
  (* because we don't know if they are quantified or not *)
  | [(clear,ElimOnIdent id),(None,None),None],None ->
      TacCase (with_evar,(clear,(CAst.make @@ CRef (qualid_of_ident ?loc:id.CAst.loc id.CAst.v,None),NoBindings)))
  | ic ->
      if List.exists (function ((_, ElimOnAnonHyp _),_,_) -> true | _ -> false) (fst ic)
      then
	user_err Pp.(str "Use of numbers as direct arguments of 'case' is not supported.");
      TacInductionDestruct (false,with_evar,ic)

let rec mkCLambdaN_simple_loc ?loc bll c =
  match bll with
  | ({CAst.loc = loc1}::_ as idl,bk,t) :: bll ->
      CAst.make ?loc @@ CLambdaN ([CLocalAssum (idl,bk,t)],mkCLambdaN_simple_loc ?loc:(Loc.merge_opt loc1 loc) bll c)
  | ([],_,_) :: bll -> mkCLambdaN_simple_loc ?loc bll c
  | [] -> c

let mkCLambdaN_simple bl c = match bl with
  | [] -> c
  | h :: _ ->
    let loc = Loc.merge_opt (List.hd (pi1 h)).CAst.loc (Constrexpr_ops.constr_loc c) in
    mkCLambdaN_simple_loc ?loc bl c

let loc_of_ne_list l = Loc.merge_opt (List.hd l).CAst.loc (List.last l).CAst.loc

let map_int_or_var f = function
  | ArgArg x -> ArgArg (f x)
  | ArgVar _ as y -> y

let all_concl_occs_clause = { onhyps=Some[]; concl_occs=AllOccurrences }

let merge_occurrences loc cl = function
  | None ->
      if Locusops.clause_with_generic_occurrences cl then (None, cl)
      else
	user_err ~loc  (str "Found an \"at\" clause without \"with\" clause.")
  | Some (occs, p) ->
    let ans = match occs with
    | AllOccurrences -> cl
    | _ ->
      begin match cl with
      | { onhyps = Some []; concl_occs = AllOccurrences } ->
        { onhyps = Some []; concl_occs = occs }
      | { onhyps = Some [(AllOccurrences, id), l]; concl_occs = NoOccurrences } ->
        { cl with onhyps = Some [(occs, id), l] }
      | _ ->
        if Locusops.clause_with_generic_occurrences cl then
          user_err ~loc  (str "Unable to interpret the \"at\" clause; move it in the \"in\" clause.")
        else
          user_err ~loc  (str "Cannot use clause \"at\" twice.")
      end
    in
    (Some p, ans)

let warn_deprecated_eqn_syntax =
  CWarnings.create ~name:"deprecated-eqn-syntax" ~category:"deprecated"
         (fun arg -> strbrk (Printf.sprintf "Syntax \"_eqn:%s\" is deprecated. Please use \"eqn:%s\" instead." arg arg))

(* Auxiliary grammar rules *)

open Pvernac.Vernac_


let _ = let nat_or_var = Gram.Entry.create "nat_or_var"
        and id_or_meta = Gram.Entry.create "id_or_meta"
        and constr_with_bindings_arg =
          Gram.Entry.create "constr_with_bindings_arg"
        and conversion = Gram.Entry.create "conversion"
        and occs_nums = Gram.Entry.create "occs_nums"
        and occs = Gram.Entry.create "occs"
        and pattern_occ = Gram.Entry.create "pattern_occ"
        and ref_or_pattern_occ = Gram.Entry.create "ref_or_pattern_occ"
        and unfold_occ = Gram.Entry.create "unfold_occ"
        and intropatterns = Gram.Entry.create "intropatterns"
        and ne_intropatterns = Gram.Entry.create "ne_intropatterns"
        and or_and_intropattern = Gram.Entry.create "or_and_intropattern"
        and equality_intropattern = Gram.Entry.create "equality_intropattern"
        and naming_intropattern = Gram.Entry.create "naming_intropattern"
        and nonsimple_intropattern =
          Gram.Entry.create "nonsimple_intropattern"
        and simple_intropattern_closed =
          Gram.Entry.create "simple_intropattern_closed"
        and simple_binding = Gram.Entry.create "simple_binding"
        and with_bindings = Gram.Entry.create "with_bindings"
        and red_flags = Gram.Entry.create "red_flags"
        and delta_flag = Gram.Entry.create "delta_flag"
        and strategy_flag = Gram.Entry.create "strategy_flag"
        and hypident_occ = Gram.Entry.create "hypident_occ"
        and clause_dft_all = Gram.Entry.create "clause_dft_all"
        and opt_clause = Gram.Entry.create "opt_clause"
        and concl_occ = Gram.Entry.create "concl_occ"
        and in_hyp_list = Gram.Entry.create "in_hyp_list"
        and in_hyp_as = Gram.Entry.create "in_hyp_as"
        and orient = Gram.Entry.create "orient"
        and simple_binder = Gram.Entry.create "simple_binder"
        and fixdecl = Gram.Entry.create "fixdecl"
        and fixannot = Gram.Entry.create "fixannot"
        and cofixdecl = Gram.Entry.create "cofixdecl"
        and bindings_with_parameters =
          Gram.Entry.create "bindings_with_parameters"
        and eliminator = Gram.Entry.create "eliminator"
        and as_ipat = Gram.Entry.create "as_ipat"
        and or_and_intropattern_loc =
          Gram.Entry.create "or_and_intropattern_loc"
        and as_or_and_ipat = Gram.Entry.create "as_or_and_ipat"
        and eqn_ipat = Gram.Entry.create "eqn_ipat"
        and as_name = Gram.Entry.create "as_name"
        and by_tactic = Gram.Entry.create "by_tactic"
        and rewriter = Gram.Entry.create "rewriter"
        and oriented_rewriter = Gram.Entry.create "oriented_rewriter"
        and induction_clause = Gram.Entry.create "induction_clause"
        and induction_clause_list = Gram.Entry.create "induction_clause_list"
        in
        let () =
        Gram.gram_extend int_or_var
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry identref)),
                 (fun id loc ->  ArgVar id ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry integer)),
                (fun n loc ->  ArgArg n ))])])
        in let () =
        Gram.gram_extend nat_or_var
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry identref)),
                 (fun id loc ->  ArgVar id ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry natural)),
                (fun n loc ->  ArgArg n ))])])
        in let () =
        Gram.gram_extend id_or_meta
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry identref)),
                 (fun id loc ->  id ))])])
        in let () =
        Gram.gram_extend open_constr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry constr)),
                 (fun c loc ->  c ))])])
        in let () =
        Gram.gram_extend uconstr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry constr)),
                 (fun c loc ->  c ))])])
        in let () =
        Gram.gram_extend destruction_arg
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentry constr_with_bindings_arg)),
                 (fun c loc ->  on_snd destruction_arg_of_constr c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry test_lpar_id_rpar)),
                             (Extend.Aentry constr_with_bindings)),
                (fun c _ loc ->  (Some false,destruction_arg_of_constr c) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry natural)),
                (fun n loc ->  (None,ElimOnAnonHyp n) ))])])
        in let () =
        Gram.gram_extend constr_with_bindings_arg
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentry constr_with_bindings)),
                 (fun c loc ->  (None,c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD ">"))),
                             (Extend.Aentry constr_with_bindings)),
                (fun c _ loc ->  (Some true,c) ))])])
        in let () =
        Gram.gram_extend quantified_hypothesis
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry natural)),
                 (fun n loc ->  AnonHyp n ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                (fun id loc ->  NamedHyp id ))])])
        in let () =
        Gram.gram_extend conversion
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry constr)),
                                                        (Extend.Atoken (Tok.KEYWORD "at"))),
                                                        (Extend.Aentry occs_nums)),
                                           (Extend.Atoken (Tok.KEYWORD "with"))),
                              (Extend.Aentry constr)),
                 (fun c2 _ occs _ c1 loc ->  (Some (occs,c1), c2) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry constr)),
                                          (Extend.Atoken (Tok.KEYWORD "with"))),
                             (Extend.Aentry constr)),
                (fun c2 _ c1 loc ->  (Some (AllOccurrences,c1),c2) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry constr)),
                (fun c loc ->  (None, c) ))])])
        in let () =
        Gram.gram_extend occs_nums
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "-"))),
                                           (Extend.Aentry nat_or_var)),
                              (Extend.Alist0 (Extend.Aentry int_or_var))),
                 (fun nl n _ loc ->
                  AllOccurrencesBut (List.map (map_int_or_var abs) (n::nl)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Alist1 (Extend.Aentry nat_or_var))),
                (fun nl loc ->  OnlyOccurrences nl ))])])
        in let () =
        Gram.gram_extend occs
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  AllOccurrences ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "at"))),
                             (Extend.Aentry occs_nums)),
                (fun occs _ loc ->  occs ))])])
        in let () =
        Gram.gram_extend pattern_occ
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry constr)),
                              (Extend.Aentry occs)),
                 (fun nl c loc ->  (nl,c) ))])])
        in let () =
        Gram.gram_extend ref_or_pattern_occ
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry constr)),
                              (Extend.Aentry occs)),
                 (fun nl c loc ->  nl,Inr c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry smart_global)),
                             (Extend.Aentry occs)),
                (fun nl c loc ->  nl,Inl c ))])])
        in let () =
        Gram.gram_extend unfold_occ
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry smart_global)),
                              (Extend.Aentry occs)),
                 (fun nl c loc ->  (nl,c) ))])])
        in let () =
        Gram.gram_extend intropatterns
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist0 (Extend.Aentry nonsimple_intropattern))),
                 (fun l loc ->  l ))])])
        in let () =
        Gram.gram_extend ne_intropatterns
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist1 (Extend.Aentry nonsimple_intropattern))),
                 (fun l loc ->  l ))])])
        in let () =
        Gram.gram_extend or_and_intropattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Aentry simple_intropattern)),
                                                        (Extend.Atoken (Tok.KEYWORD "&"))),
                                           (Extend.Alist1sep ((Extend.Aentry simple_intropattern), (Extend.Atoken (Tok.KEYWORD "&"))))),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ tc _ si _ loc ->
                  let rec pairify = function
	    | ([]|[_]|[_;_]) as l -> l
            | t::q -> [t; CAst.make ?loc:(loc_of_ne_list q) (IntroAction (IntroOrAndPattern (IntroAndPattern (pairify q))))]
	  in IntroAndPattern (pairify (si::tc)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry simple_intropattern)),
                                                       (Extend.Atoken (Tok.KEYWORD ","))),
                                          (Extend.Alist1sep ((Extend.Aentry simple_intropattern), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ tc _ si _ loc ->  IntroAndPattern (si::tc) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "("))),
                                          (Extend.Aentry simple_intropattern)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ si _ loc ->  IntroAndPattern [si] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "()"))),
                (fun _ loc ->  IntroAndPattern [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "["))),
                                          (Extend.Alist1sep ((Extend.Aentry intropatterns), (Extend.Atoken (Tok.KEYWORD "|"))))),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ tc _ loc ->  IntroOrPattern tc ))])])
        in let () =
        Gram.gram_extend equality_intropattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "[="))),
                                           (Extend.Aentry intropatterns)),
                              (Extend.Atoken (Tok.KEYWORD "]"))),
                 (fun _ tc _ loc ->  IntroInjection tc ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "<-"))),
                (fun _ loc ->  IntroRewrite false ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "->"))),
                (fun _ loc ->  IntroRewrite true ))])])
        in let () =
        Gram.gram_extend naming_intropattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                 (fun id loc ->  IntroIdentifier id ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "?"))),
                (fun _ loc ->  IntroAnonymous ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry pattern_ident)),
                (fun prefix loc ->  IntroFresh prefix ))])])
        in let () =
        Gram.gram_extend nonsimple_intropattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.KEYWORD "**"))),
                 (fun _ loc ->  CAst.make ~loc @@ IntroForthcoming false ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "*"))),
                (fun _ loc ->  CAst.make ~loc @@ IntroForthcoming true ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentry simple_intropattern)),
                (fun l loc ->  l ))])])
        in let () =
        Gram.gram_extend simple_intropattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry simple_intropattern_closed)),
                              (Extend.Alist0 (Extend.Arules [Extend.Rules 
                                                            ({ Extend.norec_rule = Extend.Next 
                                                            (Extend.Next 
                                                            (Extend.Stop,
                                                            (Extend.Atoken (Tok.KEYWORD "%"))),
                                                            (Extend.Aentryl (operconstr, "0"))) },
                                                            (fun c _ loc ->
                                                             c ))]))),
                 (fun l pat loc ->
                  let {CAst.loc=loc0;v=pat} = pat in
          let f c pat =
            let loc1 = Constrexpr_ops.constr_loc c in
            let loc = Loc.merge_opt loc0 loc1 in
            IntroAction (IntroApplyOn (CAst.(make ?loc:loc1 c),CAst.(make ?loc pat))) in
          CAst.make ~loc @@ List.fold_right f l pat ))])])
        in let () =
        Gram.gram_extend simple_intropattern_closed
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentry naming_intropattern)),
                 (fun pat loc ->  CAst.make ~loc @@ IntroNaming pat ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "_"))),
                (fun _ loc ->  CAst.make ~loc @@ IntroAction IntroWildcard ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentry equality_intropattern)),
                (fun pat loc ->  CAst.make ~loc @@ IntroAction pat ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentry or_and_intropattern)),
                (fun pat loc ->
                 CAst.make ~loc @@ IntroAction (IntroOrAndPattern pat) ))])])
        in let () =
        Gram.gram_extend simple_binding
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Aentry natural)),
                                                        (Extend.Atoken (Tok.KEYWORD ":="))),
                                           (Extend.Aentry lconstr)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ c _ n _ loc ->  CAst.make ~loc (AnonHyp n, c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry ident)),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ id _ loc ->  CAst.make ~loc (NamedHyp id, c) ))])])
        in let () =
        Gram.gram_extend bindings
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist1 (Extend.Aentry constr))),
                 (fun bl loc ->  ImplicitBindings bl ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry test_lpar_idnum_coloneq)),
                             (Extend.Alist1 (Extend.Aentry simple_binding))),
                (fun bl _ loc ->  ExplicitBindings bl ))])])
        in let () =
        Gram.gram_extend constr_with_bindings
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry constr)),
                              (Extend.Aentry with_bindings)),
                 (fun l c loc ->  (c, l) ))])])
        in let () =
        Gram.gram_extend with_bindings
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  NoBindings ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "with"))),
                             (Extend.Aentry bindings)),
                (fun bl _ loc ->  bl ))])])
        in let () =
        Gram.gram_extend red_flags
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT "delta"))),
                              (Extend.Aentry delta_flag)),
                 (fun d _ loc ->  [d] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "zeta"))),
                (fun _ loc ->  [FZeta] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "cofix"))),
                (fun _ loc ->  [FCofix] ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "fix"))),
                (fun _ loc ->  [FFix] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "match"))),
                (fun _ loc ->  [FMatch] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "iota"))),
                (fun _ loc ->  [FMatch;FFix;FCofix] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "beta"))),
                (fun _ loc ->  [FBeta] ))])])
        in let () =
        Gram.gram_extend delta_flag
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  FDeltaBut [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "["))),
                                          (Extend.Alist1 (Extend.Aentry smart_global))),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ idl _ loc ->  FConst idl ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "-"))),
                                                       (Extend.Atoken (Tok.KEYWORD "["))),
                                          (Extend.Alist1 (Extend.Aentry smart_global))),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ idl _ _ loc ->  FDeltaBut idl ))])])
        in let () =
        Gram.gram_extend strategy_flag
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry delta_flag)),
                 (fun d loc ->  all_with d ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Alist1 (Extend.Aentry red_flags))),
                (fun s loc ->  Redops.make_red_flag (List.flatten s) ))])])
        in let () =
        Gram.gram_extend red_expr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT ""))),
                 (fun s loc ->  ExtraRedExpr s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "pattern"))),
                             (Extend.Alist1sep ((Extend.Aentry pattern_occ), (Extend.Atoken (Tok.KEYWORD ","))))),
                (fun pl _ loc ->  Pattern pl ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "fold"))),
                             (Extend.Alist1 (Extend.Aentry constr))),
                (fun cl _ loc ->  Fold cl ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "unfold"))),
                             (Extend.Alist1sep ((Extend.Aentry unfold_occ), (Extend.Atoken (Tok.KEYWORD ","))))),
                (fun ul _ loc ->  Unfold ul ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "native_compute"))),
                             (Extend.Aopt (Extend.Aentry ref_or_pattern_occ))),
                (fun po _ loc ->  CbvNative po ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "vm_compute"))),
                             (Extend.Aopt (Extend.Aentry ref_or_pattern_occ))),
                (fun po _ loc ->  CbvVm po ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "compute"))),
                             (Extend.Aentry delta_flag)),
                (fun delta _ loc ->  Cbv (all_with delta) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "lazy"))),
                             (Extend.Aentry strategy_flag)),
                (fun s _ loc ->  Lazy s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "cbn"))),
                             (Extend.Aentry strategy_flag)),
                (fun s _ loc ->  Cbn s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "cbv"))),
                             (Extend.Aentry strategy_flag)),
                (fun s _ loc ->  Cbv s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "simpl"))),
                                          (Extend.Aentry delta_flag)),
                             (Extend.Aopt (Extend.Aentry ref_or_pattern_occ))),
                (fun po d _ loc ->  Simpl (all_with d,po) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "hnf"))),
                (fun _ loc ->  Hnf ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "red"))),
                (fun _ loc ->  Red false ))])])
        in let () =
        Gram.gram_extend hypident
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Atoken (Tok.IDENT "value"))),
                                                        (Extend.Atoken (Tok.IDENT "of"))),
                                           (Extend.Aentry id_or_meta)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ id _ _ _ loc ->
                  let id : lident = id in
        id,InHypValueOnly ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Atoken (Tok.IDENT "type"))),
                                                       (Extend.Atoken (Tok.IDENT "of"))),
                                          (Extend.Aentry id_or_meta)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ id _ _ _ loc ->
                 let id : lident = id in
        id,InHypTypeOnly ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry id_or_meta)),
                (fun id loc ->  let id : lident = id in
        id,InHyp ))])])
        in let () =
        Gram.gram_extend hypident_occ
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry hypident)),
                              (Extend.Aentry occs)),
                 (fun occs h loc ->
                  let (id,l) = h in
        let id : lident = id in
        ((occs,id),l) ))])])
        in let () =
        Gram.gram_extend in_clause
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist0sep ((Extend.Aentry hypident_occ), (Extend.Atoken (Tok.KEYWORD ","))))),
                 (fun hl loc ->  {onhyps=Some hl; concl_occs=NoOccurrences} ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Alist0sep ((Extend.Aentry hypident_occ), (Extend.Atoken (Tok.KEYWORD ","))))),
                                          (Extend.Atoken (Tok.KEYWORD "|-"))),
                             (Extend.Aentry concl_occ)),
                (fun occs _ hl loc ->  {onhyps=Some hl; concl_occs=occs} ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "*"))),
                                          (Extend.Atoken (Tok.KEYWORD "|-"))),
                             (Extend.Aentry concl_occ)),
                (fun occs _ _ loc ->  {onhyps=None; concl_occs=occs} ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "*"))),
                             (Extend.Aentry occs)),
                (fun occs _ loc ->  {onhyps=None; concl_occs=occs} ))])])
        in let () =
        Gram.gram_extend clause_dft_concl
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->  all_concl_occs_clause ));
                Extend.Rule (Extend.Next (Extend.Stop, (Extend.Aentry occs)),
                (fun occs loc ->  {onhyps=Some[]; concl_occs=occs} ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentry in_clause)),
                (fun cl _ loc ->  cl ))])])
        in let () =
        Gram.gram_extend clause_dft_all
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->  {onhyps=None; concl_occs=AllOccurrences} ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentry in_clause)),
                (fun cl _ loc ->  cl ))])])
        in let () =
        Gram.gram_extend opt_clause
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "at"))),
                             (Extend.Aentry occs_nums)),
                (fun occs _ loc ->  Some {onhyps=Some[]; concl_occs=occs} ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentry in_clause)),
                (fun cl _ loc ->  Some cl ))])])
        in let () =
        Gram.gram_extend concl_occ
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  NoOccurrences ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "*"))),
                             (Extend.Aentry occs)),
                (fun occs _ loc ->  occs ))])])
        in let () =
        Gram.gram_extend in_hyp_list
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Alist1 (Extend.Aentry id_or_meta))),
                (fun idl _ loc ->  idl ))])])
        in let () =
        Gram.gram_extend in_hyp_as
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "in"))),
                                          (Extend.Aentry id_or_meta)),
                             (Extend.Aentry as_ipat)),
                (fun ipat id _ loc ->  Some (id,ipat) ))])])
        in let () =
        Gram.gram_extend orient
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  true ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "<-"))),
                (fun _ loc ->  false ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "->"))),
                (fun _ loc ->  true ))])])
        in let () =
        Gram.gram_extend simple_binder
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Alist1 (Extend.Aentry name))),
                                                        (Extend.Atoken (Tok.KEYWORD ":"))),
                                           (Extend.Aentry lconstr)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ c _ nal _ loc ->  (nal,Default Explicit,c) ));
                Extend.Rule (Extend.Next (Extend.Stop, (Extend.Aentry name)),
                (fun na loc ->
                 ([na],Default Explicit, CAst.make ~loc @@
                    CHole (Some (Evar_kinds.BinderType na.CAst.v), IntroAnonymous, None)) ))])])
        in let () =
        Gram.gram_extend fixdecl
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Aentry ident)),
                                                        (Extend.Alist0 (Extend.Aentry simple_binder))),
                                                        (Extend.Aentry fixannot)),
                                                        (Extend.Atoken (Tok.KEYWORD ":"))),
                                           (Extend.Aentry lconstr)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ ty _ ann bl id _ loc ->  (loc, id, bl, ann, ty) ))])])
        in let () =
        Gram.gram_extend fixannot
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "{"))),
                                                       (Extend.Atoken (Tok.IDENT "struct"))),
                                          (Extend.Aentry name)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ id _ _ loc ->  Some id ))])])
        in let () =
        Gram.gram_extend cofixdecl
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Aentry ident)),
                                                        (Extend.Alist0 (Extend.Aentry simple_binder))),
                                                        (Extend.Atoken (Tok.KEYWORD ":"))),
                                           (Extend.Aentry lconstr)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ ty _ bl id _ loc ->  (loc, id, bl, None, ty) ))])])
        in let () =
        Gram.gram_extend bindings_with_parameters
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry check_for_coloneq)),
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Aentry ident)),
                                                        (Extend.Alist0 (Extend.Aentry simple_binder))),
                                                        (Extend.Atoken (Tok.KEYWORD ":="))),
                                           (Extend.Aentry lconstr)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ c _ bl id _ _ loc ->  (id, mkCLambdaN_simple bl c) ))])])
        in let () =
        Gram.gram_extend eliminator
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "using"))),
                              (Extend.Aentry constr_with_bindings)),
                 (fun el _ loc ->  el ))])])
        in let () =
        Gram.gram_extend as_ipat
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                             (Extend.Aentry simple_intropattern)),
                (fun ipat _ loc ->  Some ipat ))])])
        in let () =
        Gram.gram_extend or_and_intropattern_loc
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry identref)),
                 (fun locid loc ->  ArgVar locid ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentry or_and_intropattern)),
                (fun ipat loc ->  ArgArg (CAst.make ~loc ipat) ))])])
        in let () =
        Gram.gram_extend as_or_and_ipat
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                             (Extend.Aentry or_and_intropattern_loc)),
                (fun ipat _ loc ->  Some ipat ))])])
        in let () =
        Gram.gram_extend eqn_ipat
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "_eqn"))),
                (fun _ loc ->
                 warn_deprecated_eqn_syntax ~loc "?"; Some (CAst.make ~loc IntroAnonymous) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "_eqn"))),
                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                             (Extend.Aentry naming_intropattern)),
                (fun pat _ _ loc ->
                 warn_deprecated_eqn_syntax ~loc "H"; Some (CAst.make ~loc pat) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "eqn"))),
                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                             (Extend.Aentry naming_intropattern)),
                (fun pat _ _ loc ->  Some (CAst.make ~loc pat) ))])])
        in let () =
        Gram.gram_extend as_name
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->  Names.Name.Anonymous ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                             (Extend.Aentry ident)),
                (fun id _ loc ->  Names.Name.Name id ))])])
        in let () =
        Gram.gram_extend by_tactic
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "by"))),
                             (Extend.Aentryl (tactic_expr, "3"))),
                (fun tac _ loc ->  Some tac ))])])
        in let () =
        Gram.gram_extend rewriter
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentry constr_with_bindings_arg)),
                 (fun c loc ->  (Equality.Precisely 1, c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry natural)),
                             (Extend.Aentry constr_with_bindings_arg)),
                (fun c n loc ->  (Equality.Precisely n,c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry natural)),
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.LEFTQMARK))) },
                                                         (fun _ loc -> 
                                                          () ));
                                                         Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "?"))) },
                                                         (fun _ loc -> 
                                                          () ))])),
                             (Extend.Aentry constr_with_bindings_arg)),
                (fun c _ n loc ->  (Equality.UpTo n,c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry natural)),
                                          (Extend.Atoken (Tok.KEYWORD "!"))),
                             (Extend.Aentry constr_with_bindings_arg)),
                (fun c _ n loc ->  (Equality.Precisely n,c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.LEFTQMARK))) },
                                                         (fun _ loc -> 
                                                          () ));
                                                         Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "?"))) },
                                                         (fun _ loc -> 
                                                          () ))])),
                             (Extend.Aentry constr_with_bindings_arg)),
                (fun c _ loc ->  (Equality.RepeatStar,c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "!"))),
                             (Extend.Aentry constr_with_bindings_arg)),
                (fun c _ loc ->  (Equality.RepeatPlus,c) ))])])
        in let () =
        Gram.gram_extend oriented_rewriter
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry orient)),
                              (Extend.Aentry rewriter)),
                 (fun p b loc ->  let (m,c) = p in (b,m,c) ))])])
        in let () =
        Gram.gram_extend induction_clause
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry destruction_arg)),
                                                        (Extend.Aentry as_or_and_ipat)),
                                           (Extend.Aentry eqn_ipat)),
                              (Extend.Aentry opt_clause)),
                 (fun cl eq pat c loc ->  (c,(eq,pat),cl) ))])])
        in let () =
        Gram.gram_extend induction_clause_list
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Alist1sep ((Extend.Aentry induction_clause), (Extend.Atoken (Tok.KEYWORD ","))))),
                                           (Extend.Aopt (Extend.Aentry eliminator))),
                              (Extend.Aentry opt_clause)),
                 (fun cl_tolerance el ic loc ->
                  match ic,el,cl_tolerance with
        | [c,pat,None],Some _,Some _ -> ([c,pat,cl_tolerance],el)
        | _,_,Some _ -> err ()
        | _,_,None -> (ic,el) ))])])
        in let () =
        Gram.gram_extend simple_tactic
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "change"))),
                                           (Extend.Aentry conversion)),
                              (Extend.Aentry clause_dft_concl)),
                 (fun cl c _ loc ->
                  let (oc, c) = c in
	  let p,cl = merge_occurrences loc cl oc in
	  TacAtom (Loc.tag ~loc @@ TacChange (p,c,cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "pattern"))),
                                          (Extend.Alist1sep ((Extend.Aentry pattern_occ), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl pl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Pattern pl, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "fold"))),
                                          (Extend.Alist1 (Extend.Aentry constr))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl l _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Fold l, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "unfold"))),
                                          (Extend.Alist1sep ((Extend.Aentry unfold_occ), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl ul _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Unfold ul, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "native_compute"))),
                                          (Extend.Aopt (Extend.Aentry ref_or_pattern_occ))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl po _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (CbvNative po, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "vm_compute"))),
                                          (Extend.Aopt (Extend.Aentry ref_or_pattern_occ))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl po _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (CbvVm po, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "compute"))),
                                          (Extend.Aentry delta_flag)),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl delta _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Cbv (all_with delta), cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "lazy"))),
                                          (Extend.Aentry strategy_flag)),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl s _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Lazy s, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "cbn"))),
                                          (Extend.Aentry strategy_flag)),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl s _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Cbn s, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "cbv"))),
                                          (Extend.Aentry strategy_flag)),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl s _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Cbv s, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "simpl"))),
                                                       (Extend.Aentry delta_flag)),
                                          (Extend.Aopt (Extend.Aentry ref_or_pattern_occ))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl po d _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Simpl (all_with d, po), cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "hnf"))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Hnf, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "red"))),
                             (Extend.Aentry clause_dft_concl)),
                (fun cl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacReduce (Red false, cl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "inversion"))),
                                                                    (Extend.Aentry quantified_hypothesis)),
                                                       (Extend.Atoken (Tok.KEYWORD "using"))),
                                          (Extend.Aentry constr)),
                             (Extend.Aentry in_hyp_list)),
                (fun cl c _ hyp _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInversion (InversionUsing (c,cl), hyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "inversion_clear"))),
                                                       (Extend.Aentry quantified_hypothesis)),
                                          (Extend.Aentry as_or_and_ipat)),
                             (Extend.Aentry in_hyp_list)),
                (fun cl ids hyp _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInversion (NonDepInversion (FullInversionClear, cl, ids), hyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "inversion"))),
                                                       (Extend.Aentry quantified_hypothesis)),
                                          (Extend.Aentry as_or_and_ipat)),
                             (Extend.Aentry in_hyp_list)),
                (fun cl ids hyp _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInversion (NonDepInversion (FullInversion, cl, ids), hyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "simple"))),
                                                                    (Extend.Atoken (Tok.IDENT "inversion"))),
                                                       (Extend.Aentry quantified_hypothesis)),
                                          (Extend.Aentry as_or_and_ipat)),
                             (Extend.Aentry in_hyp_list)),
                (fun cl ids hyp _ _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInversion (NonDepInversion (SimpleInversion, cl, ids), hyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "dependent"))),
                                                                    (Extend.Arules 
                                                                    [Extend.Rules 
                                                                    ({ Extend.norec_rule = Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "inversion_clear"))) },
                                                                    (fun _
                                                                    loc ->
                                                                     FullInversionClear ));
                                                                    Extend.Rules 
                                                                    ({ Extend.norec_rule = Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "inversion"))) },
                                                                    (fun _
                                                                    loc ->
                                                                     FullInversion ));
                                                                    Extend.Rules 
                                                                    ({ Extend.norec_rule = Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "simple"))),
                                                                    (Extend.Atoken (Tok.IDENT "inversion"))) },
                                                                    (fun _ _
                                                                    loc ->
                                                                     SimpleInversion ))])),
                                                       (Extend.Aentry quantified_hypothesis)),
                                          (Extend.Aentry as_or_and_ipat)),
                             (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "with"))),
                                                         (Extend.Aentry constr)) },
                                                         (fun c _ loc ->
                                                          c ))]))),
                (fun co ids hyp k _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInversion (DepInversion (k,co,ids),hyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "erewrite"))),
                                                       (Extend.Alist1sep ((Extend.Aentry oriented_rewriter), (Extend.Atoken (Tok.KEYWORD ","))))),
                                          (Extend.Aentry clause_dft_concl)),
                             (Extend.Aentry by_tactic)),
                (fun t cl l _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacRewrite (true,l,cl,t)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "rewrite"))),
                                                       (Extend.Alist1sep ((Extend.Aentry oriented_rewriter), (Extend.Atoken (Tok.KEYWORD ","))))),
                                          (Extend.Aentry clause_dft_concl)),
                             (Extend.Aentry by_tactic)),
                (fun t cl l _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacRewrite (false,l,cl,t)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "edestruct"))),
                             (Extend.Aentry induction_clause_list)),
                (fun icl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInductionDestruct(false,true,icl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "destruct"))),
                             (Extend.Aentry induction_clause_list)),
                (fun icl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInductionDestruct(false,false,icl)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "einduction"))),
                             (Extend.Aentry induction_clause_list)),
                (fun ic _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInductionDestruct(true,true,ic)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "induction"))),
                             (Extend.Aentry induction_clause_list)),
                (fun ic _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacInductionDestruct (true,false,ic)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "generalize"))),
                                                                    (Extend.Aentry constr)),
                                                                    (Extend.Aentry lookup_at_as_comma)),
                                                       (Extend.Aentry occs)),
                                          (Extend.Aentry as_name)),
                             (Extend.Alist0 (Extend.Arules [Extend.Rules 
                                                           ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Atoken (Tok.KEYWORD ","))),
                                                           (Extend.Aentry pattern_occ)),
                                                           (Extend.Aentry as_name)) },
                                                           (fun na c _ loc ->
                                                            (c,na) ))]))),
                (fun l na nl _ c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacGeneralize (((nl,c),na)::l)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "generalize"))),
                                          (Extend.Aentry constr)),
                             (Extend.Alist1 (Extend.Aentry constr))),
                (fun l c _ loc ->
                 let gen_everywhere c = ((AllOccurrences,c),Names.Name.Anonymous) in
          TacAtom (Loc.tag ~loc @@ TacGeneralize (List.map gen_everywhere (c::l))) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "generalize"))),
                             (Extend.Aentry constr)),
                (fun c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacGeneralize [((AllOccurrences,c),Names.Name.Anonymous)]) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "eenough"))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Aentry as_ipat)),
                             (Extend.Aentry by_tactic)),
                (fun tac ipat c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacAssert (true,false,Some tac,ipat,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "enough"))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Aentry as_ipat)),
                             (Extend.Aentry by_tactic)),
                (fun tac ipat c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacAssert (false,false,Some tac,ipat,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "epose"))),
                                                       (Extend.Atoken (Tok.IDENT "proof"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Aentry as_ipat)),
                (fun ipat c _ _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacAssert (true,true,None,ipat,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "pose"))),
                                                       (Extend.Atoken (Tok.IDENT "proof"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Aentry as_ipat)),
                (fun ipat c _ _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacAssert (false,true,None,ipat,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "eassert"))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Aentry as_ipat)),
                             (Extend.Aentry by_tactic)),
                (fun tac ipat c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacAssert (true,true,Some tac,ipat,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "assert"))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Aentry as_ipat)),
                             (Extend.Aentry by_tactic)),
                (fun tac ipat c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacAssert (false,true,Some tac,ipat,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "eenough"))),
                                                                    (Extend.Aentry test_lpar_id_colon)),
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry identref)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Aentry lconstr)),
                                          (Extend.Atoken (Tok.KEYWORD ")"))),
                             (Extend.Aentry by_tactic)),
                (fun tac _ c _ lid _ _ _ loc ->
                 let { CAst.loc = loc; v = id } = lid in
          TacAtom (Loc.tag ?loc @@ TacAssert (true,false,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "enough"))),
                                                                    (Extend.Aentry test_lpar_id_colon)),
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry identref)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Aentry lconstr)),
                                          (Extend.Atoken (Tok.KEYWORD ")"))),
                             (Extend.Aentry by_tactic)),
                (fun tac _ c _ lid _ _ _ loc ->
                 let { CAst.loc = loc; v = id } = lid in
          TacAtom (Loc.tag ?loc @@ TacAssert (false,false,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "eassert"))),
                                                                    (Extend.Aentry test_lpar_id_colon)),
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry identref)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Aentry lconstr)),
                                          (Extend.Atoken (Tok.KEYWORD ")"))),
                             (Extend.Aentry by_tactic)),
                (fun tac _ c _ lid _ _ _ loc ->
                 let { CAst.loc = loc; v = id } = lid in
          TacAtom (Loc.tag ?loc @@ TacAssert (true,true,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "assert"))),
                                                                    (Extend.Aentry test_lpar_id_colon)),
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry identref)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Aentry lconstr)),
                                          (Extend.Atoken (Tok.KEYWORD ")"))),
                             (Extend.Aentry by_tactic)),
                (fun tac _ c _ lid _ _ _ loc ->
                 let { CAst.loc = loc; v = id } = lid in
          TacAtom (Loc.tag ?loc @@ TacAssert (false,true,Some tac,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "eassert"))),
                                                                    (Extend.Aentry test_lpar_id_coloneq)),
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry identref)),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ lid _ _ _ loc ->
                 let { CAst.loc = loc; v = id } = lid in
          TacAtom (Loc.tag ?loc @@ TacAssert (true,true,None,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "assert"))),
                                                                    (Extend.Aentry test_lpar_id_coloneq)),
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry identref)),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ lid _ _ _ loc ->
                 let { CAst.loc = loc; v = id } = lid in
          TacAtom (Loc.tag ?loc @@ TacAssert (false,true,None,Some (CAst.make ?loc @@ IntroNaming (IntroIdentifier id)),c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "eremember"))),
                                                                    (Extend.Aentry constr)),
                                                       (Extend.Aentry as_name)),
                                          (Extend.Aentry eqn_ipat)),
                             (Extend.Aentry clause_dft_all)),
                (fun p e na c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacLetTac (true,na,c,p,false,e)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "remember"))),
                                                                    (Extend.Aentry constr)),
                                                       (Extend.Aentry as_name)),
                                          (Extend.Aentry eqn_ipat)),
                             (Extend.Aentry clause_dft_all)),
                (fun p e na c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacLetTac (false,na,c,p,false,e)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "eset"))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Aentry as_name)),
                             (Extend.Aentry clause_dft_concl)),
                (fun p na c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacLetTac (true,na,c,p,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "eset"))),
                                          (Extend.Aentry bindings_with_parameters)),
                             (Extend.Aentry clause_dft_concl)),
                (fun p bl _ loc ->
                 let (id,c) = bl in TacAtom (Loc.tag ~loc @@ TacLetTac (true,Names.Name id,c,p,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "set"))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Aentry as_name)),
                             (Extend.Aentry clause_dft_concl)),
                (fun p na c _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacLetTac (false,na,c,p,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "set"))),
                                          (Extend.Aentry bindings_with_parameters)),
                             (Extend.Aentry clause_dft_concl)),
                (fun p bl _ loc ->
                 let (id,c) = bl in TacAtom (Loc.tag ~loc @@ TacLetTac (false,Names.Name.Name id,c,p,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "epose"))),
                                          (Extend.Aentry constr)),
                             (Extend.Aentry as_name)),
                (fun na b _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacLetTac (true,na,b,Locusops.nowhere,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "epose"))),
                             (Extend.Aentry bindings_with_parameters)),
                (fun bl _ loc ->
                 let (id,b) = bl in TacAtom (Loc.tag ~loc @@ TacLetTac (true,Names.Name id,b,Locusops.nowhere,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "pose"))),
                                          (Extend.Aentry constr)),
                             (Extend.Aentry as_name)),
                (fun na b _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacLetTac (false,na,b,Locusops.nowhere,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "pose"))),
                             (Extend.Aentry bindings_with_parameters)),
                (fun bl _ loc ->
                 let (id,b) = bl in TacAtom (Loc.tag ~loc @@ TacLetTac (false,Names.Name.Name id,b,Locusops.nowhere,true,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "cofix"))),
                                                       (Extend.Aentry ident)),
                                          (Extend.Atoken (Tok.KEYWORD "with"))),
                             (Extend.Alist1 (Extend.Aentry cofixdecl))),
                (fun fd _ id _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacMutualCofix (id,List.map mk_cofix_tac fd)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "fix"))),
                                                                    (Extend.Aentry ident)),
                                                       (Extend.Aentry natural)),
                                          (Extend.Atoken (Tok.KEYWORD "with"))),
                             (Extend.Alist1 (Extend.Aentry fixdecl))),
                (fun fd _ n id _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacMutualFix (id,n,List.map mk_fix_tac fd)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "ecase"))),
                             (Extend.Aentry induction_clause_list)),
                (fun icl _ loc ->
                 TacAtom (Loc.tag ~loc @@ mkTacCase true icl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "case"))),
                             (Extend.Aentry induction_clause_list)),
                (fun icl _ loc ->
                 TacAtom (Loc.tag ~loc @@ mkTacCase false icl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "eelim"))),
                                          (Extend.Aentry constr_with_bindings_arg)),
                             (Extend.Aopt (Extend.Aentry eliminator))),
                (fun el cl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacElim (true,cl,el)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "elim"))),
                                          (Extend.Aentry constr_with_bindings_arg)),
                             (Extend.Aopt (Extend.Aentry eliminator))),
                (fun el cl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacElim (false,cl,el)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "simple"))),
                                                       (Extend.Atoken (Tok.IDENT "eapply"))),
                                          (Extend.Alist1sep ((Extend.Aentry constr_with_bindings_arg), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Aentry in_hyp_as)),
                (fun inhyp cl _ _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacApply (false,true,cl,inhyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "simple"))),
                                                       (Extend.Atoken (Tok.IDENT "apply"))),
                                          (Extend.Alist1sep ((Extend.Aentry constr_with_bindings_arg), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Aentry in_hyp_as)),
                (fun inhyp cl _ _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacApply (false,false,cl,inhyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "eapply"))),
                                          (Extend.Alist1sep ((Extend.Aentry constr_with_bindings_arg), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Aentry in_hyp_as)),
                (fun inhyp cl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacApply (true,true,cl,inhyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "apply"))),
                                          (Extend.Alist1sep ((Extend.Aentry constr_with_bindings_arg), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Aentry in_hyp_as)),
                (fun inhyp cl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacApply (true,false,cl,inhyp)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "eintros"))),
                             (Extend.Aentry ne_intropatterns)),
                (fun pl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacIntroPattern (true,pl)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "intros"))),
                (fun _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacIntroPattern (false,[CAst.make ~loc @@IntroForthcoming false])) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "intros"))),
                             (Extend.Aentry ne_intropatterns)),
                (fun pl _ loc ->
                 TacAtom (Loc.tag ~loc @@ TacIntroPattern (false,pl)) ))])])
        in ()


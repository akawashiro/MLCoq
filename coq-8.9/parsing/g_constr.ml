

open Names
open Constr
open Libnames
open Glob_term
open Constrexpr
open Constrexpr_ops
open Util
open Tok
open Namegen
open Decl_kinds

open Pcoq
open Pcoq.Prim
open Pcoq.Constr

(* TODO: avoid this redefinition without an extra dep to Notation_ops *)
let ldots_var = Id.of_string ".."

let constr_kw =
  [ "forall"; "fun"; "match"; "fix"; "cofix"; "with"; "in"; "for";
    "end"; "as"; "let"; "if"; "then"; "else"; "return";
    "Prop"; "Set"; "Type"; ".("; "_"; "..";
    "`{"; "`("; "{|"; "|}" ]

let _ = List.iter CLexer.add_keyword constr_kw

let mk_cast = function
    (c,(_,None)) -> c
  | (c,(_,Some ty)) ->
    let loc = Loc.merge_opt (constr_loc c) (constr_loc ty)
    in CAst.make ?loc @@ CCast(c, CastConv ty)

let binder_of_name expl { CAst.loc = loc; v = na } =
  CLocalAssum ([CAst.make ?loc na], Default expl,
    CAst.make ?loc @@ CHole (Some (Evar_kinds.BinderType na), IntroAnonymous, None))

let binders_of_names l =
  List.map (binder_of_name Explicit) l

let mk_fixb (id,bl,ann,body,(loc,tyc)) : fix_expr =
  let ty = match tyc with
      Some ty -> ty
    | None    -> CAst.make @@ CHole (None, IntroAnonymous, None) in
  (id,ann,bl,ty,body)

let mk_cofixb (id,bl,ann,body,(loc,tyc)) : cofix_expr =
  let _ = Option.map (fun { CAst.loc = aloc } ->
    CErrors.user_err ?loc:aloc
      ~hdr:"Constr:mk_cofixb"
      (Pp.str"Annotation forbidden in cofix expression.")) (fst ann) in
  let ty = match tyc with
      Some ty -> ty
    | None -> CAst.make @@ CHole (None, IntroAnonymous, None) in
  (id,bl,ty,body)

let mk_fix(loc,kw,id,dcls) =
  if kw then
    let fb : fix_expr list = List.map mk_fixb dcls in
    CAst.make ~loc @@ CFix(id,fb)
  else
    let fb : cofix_expr list = List.map mk_cofixb dcls in
    CAst.make ~loc @@ CCoFix(id,fb)

let mk_single_fix (loc,kw,dcl) =
  let (id,_,_,_,_) = dcl in mk_fix(loc,kw,id,[dcl])

let err () = raise Stream.Failure

(* Hack to parse "(x:=t)" as an explicit argument without conflicts with the *)
(* admissible notation "(x t)" *)
let lpar_id_coloneq =
  Gram.Entry.of_parser "test_lpar_id_coloneq"
    (fun strm ->
      match stream_nth 0 strm with
        | KEYWORD "(" ->
            (match stream_nth 1 strm with
	      | IDENT s ->
                  (match stream_nth 2 strm with
                    | KEYWORD ":=" ->
                        stream_njunk 3 strm;
                        Names.Id.of_string s
	            | _ -> err ())
              | _ -> err ())
        | _ -> err ())

let impl_ident_head =
  Gram.Entry.of_parser "impl_ident_head"
    (fun strm ->
      match stream_nth 0 strm with
	| KEYWORD "{" ->
	    (match stream_nth 1 strm with
	      | IDENT ("wf"|"struct"|"measure") -> err ()
	      | IDENT s ->
		  stream_njunk 2 strm;
		  Names.Id.of_string s
	      | _ -> err ())
	| _ -> err ())

let name_colon =
  Gram.Entry.of_parser "name_colon"
    (fun strm ->
      match stream_nth 0 strm with
	| IDENT s ->
            (match stream_nth 1 strm with
              | KEYWORD ":" ->
                  stream_njunk 2 strm;
                  Name (Names.Id.of_string s)
              | _ -> err ())
	| KEYWORD "_" ->
          (match stream_nth 1 strm with
              | KEYWORD ":" ->
                  stream_njunk 2 strm;
                  Anonymous
              | _ -> err ())
        | _ -> err ())

let aliasvar = function { CAst.v = CPatAlias (_, na) } -> Some na | _ -> None


let _ = let universe_expr = Gram.Entry.create "universe_expr"
        and universe = Gram.Entry.create "universe"
        and record_fields = Gram.Entry.create "record_fields"
        and record_field_declaration =
          Gram.Entry.create "record_field_declaration"
        and atomic_constr = Gram.Entry.create "atomic_constr"
        and inst = Gram.Entry.create "inst"
        and evar_instance = Gram.Entry.create "evar_instance"
        and instance = Gram.Entry.create "instance"
        and fix_constr = Gram.Entry.create "fix_constr"
        and single_fix = Gram.Entry.create "single_fix"
        and fix_kw = Gram.Entry.create "fix_kw"
        and fix_decl = Gram.Entry.create "fix_decl"
        and match_constr = Gram.Entry.create "match_constr"
        and case_item = Gram.Entry.create "case_item"
        and case_type = Gram.Entry.create "case_type"
        and return_type = Gram.Entry.create "return_type"
        and branches = Gram.Entry.create "branches"
        and mult_pattern = Gram.Entry.create "mult_pattern"
        and eqn = Gram.Entry.create "eqn"
        and record_pattern = Gram.Entry.create "record_pattern"
        and record_patterns = Gram.Entry.create "record_patterns"
        and impl_ident_tail = Gram.Entry.create "impl_ident_tail"
        and fixannot = Gram.Entry.create "fixannot"
        and impl_name_head = Gram.Entry.create "impl_name_head"
        and type_cstr = Gram.Entry.create "type_cstr"
        in
        let () =
        Gram.gram_extend Constr.ident
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry Prim.ident)),
                 (fun id loc ->  id ))])])
        in let () =
        Gram.gram_extend Prim.name
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.KEYWORD "_"))),
                 (fun _ loc ->  CAst.make ~loc Anonymous ))])])
        in let () =
        Gram.gram_extend global
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry Prim.reference)),
                 (fun r loc ->  r ))])])
        in let () =
        Gram.gram_extend constr_pattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry constr)),
                 (fun c loc ->  c ))])])
        in let () =
        Gram.gram_extend lconstr_pattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry lconstr)),
                 (fun c loc ->  c ))])])
        in let () =
        Gram.gram_extend sort
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "Type"))),
                                                        (Extend.Atoken (Tok.KEYWORD "@{"))),
                                           (Extend.Aentry universe)),
                              (Extend.Atoken (Tok.KEYWORD "}"))),
                 (fun _ u _ _ loc ->  GType u ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Type"))),
                (fun _ loc ->  GType [] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Prop"))),
                (fun _ loc ->  GProp ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Set"))),
                (fun _ loc ->  GSet ))])])
        in let () =
        Gram.gram_extend sort_family
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.KEYWORD "Type"))),
                 (fun _ loc ->  Sorts.InType ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Prop"))),
                (fun _ loc ->  Sorts.InProp ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Set"))),
                (fun _ loc ->  Sorts.InSet ))])])
        in let () =
        Gram.gram_extend universe_expr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.KEYWORD "_"))),
                 (fun _ loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry global)),
                (fun id loc ->  Some (id,0) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry global)),
                                          (Extend.Atoken (Tok.KEYWORD "+"))),
                             (Extend.Aentry natural)),
                (fun n _ id loc ->  Some (id,n) ))])])
        in let () =
        Gram.gram_extend universe
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry universe_expr)),
                 (fun u loc ->  [u] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "max"))),
                                                       (Extend.Atoken (Tok.KEYWORD "("))),
                                          (Extend.Alist1sep ((Extend.Aentry universe_expr), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ ids _ _ loc ->  ids ))])])
        in let () =
        Gram.gram_extend lconstr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentryl (operconstr, "200"))),
                 (fun c loc ->  c ))])])
        in let () =
        Gram.gram_extend constr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "@"))),
                                           (Extend.Aentry global)),
                              (Extend.Aentry instance)),
                 (fun i f _ loc ->
                  CAst.make ~loc @@ CAppExpl((None,f,i),[]) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentryl (operconstr, "8"))),
                (fun c loc ->  c ))])])
        in let () =
        Gram.gram_extend operconstr
        (None, [(Some ("200"), Some (Extend.RightA),
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry binder_constr)),
                 (fun c loc ->  c ))]);
               (Some ("100"), Some (Extend.RightA),
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry operconstr)),
                             (Extend.Atoken (Tok.KEYWORD ":>"))),
                (fun _ c1 loc ->  CAst.make ~loc @@ CCast(c1, CastCoerce) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry operconstr)),
                                         (Extend.Atoken (Tok.KEYWORD ":"))),
                            Extend.Aself),
               (fun c2 _ c1 loc ->
                CAst.make ~loc @@ CCast(c1, CastConv c2) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry operconstr)),
                                         (Extend.Atoken (Tok.KEYWORD ":"))),
                            (Extend.Aentry binder_constr)),
               (fun c2 _ c1 loc ->
                CAst.make ~loc @@ CCast(c1, CastConv c2) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry operconstr)),
                                         (Extend.Atoken (Tok.KEYWORD "<<:"))),
                            Extend.Aself),
               (fun c2 _ c1 loc ->
                CAst.make ~loc @@ CCast(c1, CastNative c2) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry operconstr)),
                                         (Extend.Atoken (Tok.KEYWORD "<<:"))),
                            (Extend.Aentry binder_constr)),
               (fun c2 _ c1 loc ->
                CAst.make ~loc @@ CCast(c1, CastNative c2) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry operconstr)),
                                         (Extend.Atoken (Tok.KEYWORD "<:"))),
                            Extend.Aself),
               (fun c2 _ c1 loc ->  CAst.make ~loc @@ CCast(c1, CastVM c2) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry operconstr)),
                                         (Extend.Atoken (Tok.KEYWORD "<:"))),
                            (Extend.Aentry binder_constr)),
               (fun c2 _ c1 loc ->  CAst.make ~loc @@ CCast(c1, CastVM c2) ))]);
               (Some ("99"), Some (Extend.RightA), []);
               (Some ("90"), Some (Extend.RightA), []);
               (Some ("10"), Some (Extend.LeftA),
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "@"))),
                                          (Extend.Aentry pattern_identref)),
                             (Extend.Alist1 (Extend.Aentry identref))),
                (fun args lid _ loc ->
                 let { CAst.loc = locid; v = id } = lid in
          let args = List.map (fun x -> CAst.make @@ CRef (qualid_of_ident ?loc:x.CAst.loc x.CAst.v, None), None) args in
          CAst.make ~loc @@ CApp((None, CAst.make ?loc:locid @@ CPatVar id),args) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                   (Extend.Atoken (Tok.KEYWORD "@"))),
                                                      (Extend.Aentry global)),
                                         (Extend.Aentry instance)),
                            (Extend.Alist0 Extend.Anext)),
               (fun args i f _ loc ->
                CAst.make ~loc @@ CAppExpl((None,f,i),args) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Stop,
                                         (Extend.Aentry operconstr)),
                            (Extend.Alist1 (Extend.Aentry appl_arg))),
               (fun args f loc ->  CAst.make ~loc @@ CApp((None,f),args) ))]);
               (Some ("9"), None,
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD ".."))),
                                          (Extend.Aentryl (operconstr, "0"))),
                             (Extend.Atoken (Tok.KEYWORD ".."))),
                (fun _ c _ loc ->
                 CAst.make ~loc @@ CAppExpl ((None, (qualid_of_ident ~loc ldots_var), None),[c]) ))]);
               (Some ("8"), None, []);
               (Some ("1"), Some (Extend.LeftA),
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry operconstr)),
                                          (Extend.Atoken (Tok.KEYWORD "%"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun key _ c loc ->  CAst.make ~loc @@ CDelimiters (key,c) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                   (Extend.Next 
                                                                   (Extend.Stop,
                                                                   (Extend.Aentry operconstr)),
                                                                   (Extend.Atoken (Tok.KEYWORD ".("))),
                                                                   (Extend.Atoken (Tok.KEYWORD "@"))),
                                                      (Extend.Aentry global)),
                                         (Extend.Alist0 (Extend.Aentryl (operconstr, "9")))),
                            (Extend.Atoken (Tok.KEYWORD ")"))),
               (fun _ args f _ _ c loc ->
                CAst.make ~loc @@ CAppExpl((Some (List.length args+1),f,None),args@[c]) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                   (Extend.Stop,
                                                                   (Extend.Aentry operconstr)),
                                                                   (Extend.Atoken (Tok.KEYWORD ".("))),
                                                      (Extend.Aentry global)),
                                         (Extend.Alist0 (Extend.Aentry appl_arg))),
                            (Extend.Atoken (Tok.KEYWORD ")"))),
               (fun _ args f _ c loc ->
                CAst.make ~loc @@ CApp((Some (List.length args+1), CAst.make @@ CRef (f,None)),args@[c,None]) ))]);
               (Some ("0"), None,
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "`("))),
                                          (Extend.Aentryl (operconstr, "200"))),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ loc ->
                 CAst.make ~loc @@ CGeneralization (Explicit, None, c) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Atoken (Tok.KEYWORD "`{"))),
                                         (Extend.Aentryl (operconstr, "200"))),
                            (Extend.Atoken (Tok.KEYWORD "}"))),
               (fun _ c _ loc ->
                CAst.make ~loc @@ CGeneralization (Implicit, None, c) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Atoken (Tok.KEYWORD "{"))),
                                         (Extend.Aentry binder_constr)),
                            (Extend.Atoken (Tok.KEYWORD "}"))),
               (fun _ c _ loc ->
                CAst.make ~loc @@ CNotation((InConstrEntrySomeLevel,"{ _ }"),([c],[],[],[])) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Atoken (Tok.KEYWORD "{|"))),
                                         (Extend.Aentry record_declaration)),
                            (Extend.Atoken (Tok.KEYWORD "|}"))),
               (fun _ c _ loc ->  c ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Atoken (Tok.KEYWORD "("))),
                                         (Extend.Aentryl (operconstr, "200"))),
                            (Extend.Atoken (Tok.KEYWORD ")"))),
               (fun _ c _ loc ->
                (match c.CAst.v with
            | CPrim (Numeral (n,true)) ->
                CAst.make ~loc @@ CNotation((InConstrEntrySomeLevel,"( _ )"),([c],[],[],[]))
            | _ -> c) ));
               Extend.Rule
               (Extend.Next (Extend.Stop, (Extend.Aentry match_constr)),
               (fun c loc ->  c ));
               Extend.Rule
               (Extend.Next (Extend.Stop, (Extend.Aentry atomic_constr)),
               (fun c loc ->  c ))])])
        in let () =
        Gram.gram_extend record_declaration
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry record_fields)),
                 (fun fs loc ->  CAst.make ~loc @@ CRecord fs ))])])
        in let () =
        Gram.gram_extend record_fields
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentry record_field_declaration)),
                (fun f loc ->  [f] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry record_field_declaration)),
                                          (Extend.Atoken (Tok.KEYWORD ";"))),
                             (Extend.Aentry record_fields)),
                (fun fs _ f loc ->  f :: fs ))])])
        in let () =
        Gram.gram_extend record_field_declaration
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry global)),
                                                        (Extend.Aentry binders)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentry lconstr)),
                 (fun c _ bl id loc ->
                  (id, if bl = [] then c else mkCLambdaN ~loc bl c) ))])])
        in let () =
        Gram.gram_extend binder_constr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry fix_constr)),
                 (fun c loc ->  c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "if"))),
                                                                    (Extend.Aentryl (operconstr, "200"))),
                                                                    (Extend.Aentry return_type)),
                                                                    (Extend.Atoken (Tok.KEYWORD "then"))),
                                                       (Extend.Aentryl (operconstr, "200"))),
                                          (Extend.Atoken (Tok.KEYWORD "else"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun b2 _ b1 _ po c _ loc ->
                 CAst.make ~loc @@ CIf (c, po, b1, b2) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "let"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "'"))),
                                                                    (Extend.Aentry pattern)),
                                                                    (Extend.Atoken (Tok.KEYWORD "in"))),
                                                                    (Extend.Aentryl (pattern, "200"))),
                                                                    (Extend.Atoken (Tok.KEYWORD ":="))),
                                                                    (Extend.Aentryl (operconstr, "200"))),
                                                       (Extend.Aentry case_type)),
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c2 _ rt c1 _ t _ p _ _ loc ->
                 CAst.make ~loc @@
            CCases (LetPatternStyle, Some rt, [c1, aliasvar p, Some t], [CAst.make ~loc ([[p]], c2)]) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "let"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "'"))),
                                                                    (Extend.Aentry pattern)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":="))),
                                                                    (Extend.Aentryl (operconstr, "200"))),
                                                       (Extend.Aentry case_type)),
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c2 _ rt c1 _ p _ _ loc ->
                 CAst.make ~loc @@
            CCases (LetPatternStyle, Some rt, [c1, aliasvar p, None], [CAst.make ~loc ([[p]], c2)]) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "let"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "'"))),
                                                                    (Extend.Aentry pattern)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":="))),
                                                       (Extend.Aentryl (operconstr, "200"))),
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c2 _ c1 _ p _ _ loc ->
                 CAst.make ~loc @@
            CCases (LetPatternStyle, None,    [c1, None, None],       [CAst.make ~loc ([[p]], c2)]) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "let"))),
                                                                    (Extend.Arules 
                                                                    [Extend.Rules 
                                                                    ({ Extend.norec_rule = Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "()"))) },
                                                                    (fun _
                                                                    loc ->
                                                                     [] ));
                                                                    Extend.Rules 
                                                                    ({ Extend.norec_rule = Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Alist0sep ((Extend.Aentry name), (Extend.Atoken (Tok.KEYWORD ","))))),
                                                                    (Extend.Atoken (Tok.KEYWORD ")"))) },
                                                                    (fun _ l
                                                                    _ loc ->
                                                                     l ))])),
                                                                    (Extend.Aentry return_type)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":="))),
                                                       (Extend.Aentryl (operconstr, "200"))),
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c2 _ c1 _ po lb _ loc ->
                 CAst.make ~loc @@ CLetTuple (lb,po,c1,c2) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "let"))),
                                                       (Extend.Aentry single_fix)),
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c _ fx _ loc ->
                 let fixp = mk_single_fix fx in
          let { CAst.loc = li; v = id } = match fixp.CAst.v with
              CFix(id,_) -> id
            | CCoFix(id,_) -> id
            | _ -> assert false in
          CAst.make ~loc @@ CLetIn( CAst.make ?loc:li @@ Name id,fixp,None,c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "let"))),
                                                                    (Extend.Aentry name)),
                                                                    (Extend.Aentry binders)),
                                                                    (Extend.Aentry type_cstr)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":="))),
                                                       (Extend.Aentryl (operconstr, "200"))),
                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c2 _ c1 _ ty bl id _ loc ->
                 let ty,c1 = match ty, c1 with
          | (_,None), { CAst.v = CCast(c, CastConv t) } -> (Loc.tag ?loc:(constr_loc t) @@ Some t), c (* Tolerance, see G_vernac.def_body *)
          | _, _ -> ty, c1 in
          CAst.make ~loc @@ CLetIn(id,mkCLambdaN ?loc:(constr_loc c1) bl c1,
                 Option.map (mkCProdN ?loc:(fst ty) bl) (snd ty), c2) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "fun"))),
                                                       (Extend.Aentry open_binders)),
                                          (Extend.Atoken (Tok.KEYWORD "=>"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c _ bl _ loc ->  mkCLambdaN ~loc bl c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "forall"))),
                                                       (Extend.Aentry open_binders)),
                                          (Extend.Atoken (Tok.KEYWORD ","))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c _ bl _ loc ->  mkCProdN ~loc bl c ))])])
        in let () =
        Gram.gram_extend appl_arg
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentryl (operconstr, "9"))),
                 (fun c loc ->  (c,None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry lpar_id_coloneq)),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c id loc ->
                 (c,Some (CAst.make ~loc @@ ExplByName id)) ))])])
        in let () =
        Gram.gram_extend atomic_constr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry pattern_ident)),
                              (Extend.Aentry evar_instance)),
                 (fun inst id loc ->  CAst.make ~loc @@ CEvar(id,inst) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "?"))),
                                                       (Extend.Atoken (Tok.KEYWORD "["))),
                                          (Extend.Aentry pattern_ident)),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ id _ _ loc ->
                 CAst.make ~loc @@  CHole (None, IntroFresh id, None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "?"))),
                                                       (Extend.Atoken (Tok.KEYWORD "["))),
                                          (Extend.Aentry ident)),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ id _ _ loc ->
                 CAst.make ~loc @@  CHole (None, IntroIdentifier id, None) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "_"))),
                (fun _ loc ->
                 CAst.make ~loc @@ CHole (None, IntroAnonymous, None) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry string)),
                (fun s loc ->  CAst.make ~loc @@ CPrim (String s) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.INT ""))),
                (fun n loc ->  CAst.make ~loc @@ CPrim (Numeral (n,true)) ));
                Extend.Rule (Extend.Next (Extend.Stop, (Extend.Aentry sort)),
                (fun s loc ->  CAst.make ~loc @@  CSort s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry global)),
                             (Extend.Aentry instance)),
                (fun i g loc ->  CAst.make ~loc @@ CRef (g,i) ))])])
        in let () =
        Gram.gram_extend inst
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry ident)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentry lconstr)),
                 (fun c _ id loc ->  (id,c) ))])])
        in let () =
        Gram.gram_extend evar_instance
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "@{"))),
                                          (Extend.Alist1sep ((Extend.Aentry inst), (Extend.Atoken (Tok.KEYWORD ";"))))),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ l _ loc ->  l ))])])
        in let () =
        Gram.gram_extend instance
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "@{"))),
                                          (Extend.Alist0 (Extend.Aentry universe_level))),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ l _ loc ->  Some l ))])])
        in let () =
        Gram.gram_extend universe_level
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry global)),
                 (fun id loc ->  GType (UNamed id) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "_"))),
                (fun _ loc ->  GType UAnonymous ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Type"))),
                (fun _ loc ->  GType UUnknown ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Prop"))),
                (fun _ loc ->  GProp ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Set"))),
                (fun _ loc ->  GSet ))])])
        in let () =
        Gram.gram_extend fix_constr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry single_fix)),
                                                        (Extend.Atoken (Tok.KEYWORD "with"))),
                                                        (Extend.Alist1sep ((Extend.Aentry fix_decl), (Extend.Atoken (Tok.KEYWORD "with"))))),
                                           (Extend.Atoken (Tok.KEYWORD "for"))),
                              (Extend.Aentry identref)),
                 (fun id _ dcls _ f loc ->
                  let (_,kw,dcl1) = f in
          mk_fix(loc,kw,id,dcl1::dcls) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry single_fix)),
                (fun fx1 loc ->  mk_single_fix fx1 ))])])
        in let () =
        Gram.gram_extend single_fix
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry fix_kw)),
                              (Extend.Aentry fix_decl)),
                 (fun dcl kw loc ->  (loc,kw,dcl) ))])])
        in let () =
        Gram.gram_extend fix_kw
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.KEYWORD "cofix"))),
                 (fun _ loc ->  false ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "fix"))),
                (fun _ loc ->  true ))])])
        in let () =
        Gram.gram_extend fix_decl
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry identref)),
                                                        (Extend.Aentry binders_fixannot)),
                                                        (Extend.Aentry type_cstr)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentryl (operconstr, "200"))),
                 (fun c _ ty bl id loc ->  (id,fst bl,snd bl,c,ty) ))])])
        in let () =
        Gram.gram_extend match_constr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "match"))),
                                                        (Extend.Alist1sep ((Extend.Aentry case_item), (Extend.Atoken (Tok.KEYWORD ","))))),
                                                        (Extend.Aopt (Extend.Aentry case_type))),
                                                        (Extend.Atoken (Tok.KEYWORD "with"))),
                                           (Extend.Aentry branches)),
                              (Extend.Atoken (Tok.KEYWORD "end"))),
                 (fun _ br _ ty ci _ loc ->
                  CAst.make ~loc @@ CCases(RegularStyle,ty,ci,br) ))])])
        in let () =
        Gram.gram_extend case_item
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentryl (operconstr, "100"))),
                                           (Extend.Aopt (Extend.Arules 
                                           [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "as"))),
                                                         (Extend.Aentry name)) },
                                                         (fun id _ loc ->
                                                          id ))]))),
                              (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "in"))),
                                                          (Extend.Aentry pattern)) },
                                                          (fun t _ loc ->
                                                           t ))]))),
                 (fun ty ona c loc ->  (c,ona,ty) ))])])
        in let () =
        Gram.gram_extend case_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "return"))),
                              (Extend.Aentryl (operconstr, "100"))),
                 (fun ty _ loc ->  ty ))])])
        in let () =
        Gram.gram_extend return_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Aopt (Extend.Arules 
                                                          [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                                                          (Extend.Aentry name)) },
                                                          (fun na _ loc ->
                                                           na ))]))),
                                                          (Extend.Aentry case_type)) },
                                                          (fun ty na loc ->
                                                           (na,ty) ))]))),
                 (fun a loc ->
                  match a with
          | None -> None, None
          | Some (na,t) -> (na, Some t) ))])])
        in let () =
        Gram.gram_extend branches
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aopt (Extend.Atoken (Tok.KEYWORD "|")))),
                              (Extend.Alist0sep ((Extend.Aentry eqn), (Extend.Atoken (Tok.KEYWORD "|"))))),
                 (fun br _ loc ->  br ))])])
        in let () =
        Gram.gram_extend mult_pattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist1sep ((Extend.Aentryl (pattern, "99")), (Extend.Atoken (Tok.KEYWORD ","))))),
                 (fun pl loc ->  pl ))])])
        in let () =
        Gram.gram_extend eqn
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Alist1sep ((Extend.Aentry mult_pattern), (Extend.Atoken (Tok.KEYWORD "|"))))),
                                           (Extend.Atoken (Tok.KEYWORD "=>"))),
                              (Extend.Aentry lconstr)),
                 (fun rhs _ pll loc ->  (CAst.make ~loc (pll,rhs)) ))])])
        in let () =
        Gram.gram_extend record_pattern
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry global)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentry pattern)),
                 (fun pat _ id loc ->  (id, pat) ))])])
        in let () =
        Gram.gram_extend record_patterns
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry record_pattern)),
                (fun p loc ->  [p] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry record_pattern)),
                             (Extend.Atoken (Tok.KEYWORD ";"))),
                (fun _ p loc ->  [p] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry record_pattern)),
                                          (Extend.Atoken (Tok.KEYWORD ";"))),
                             (Extend.Aentry record_patterns)),
                (fun ps _ p loc ->  p :: ps ))])])
        in let () =
        Gram.gram_extend pattern
        (None, [(Some ("200"), Some (Extend.RightA), []);
               (Some ("100"), Some (Extend.RightA),
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry pattern)),
                                          (Extend.Atoken (Tok.KEYWORD "|"))),
                             (Extend.Alist1sep ((Extend.Aentry pattern), (Extend.Atoken (Tok.KEYWORD "|"))))),
                (fun pl _ p loc ->  CAst.make ~loc @@ CPatOr (p::pl) ))]);
               (Some ("99"), Some (Extend.RightA), []);
               (Some ("90"), Some (Extend.RightA), []);
               (Some ("10"), Some (Extend.LeftA),
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "@"))),
                                          (Extend.Aentry Prim.reference)),
                             (Extend.Alist0 Extend.Anext)),
                (fun lp r _ loc ->
                 CAst.make ~loc @@ CPatCstr (r, Some lp, []) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Stop,
                                         (Extend.Aentry pattern)),
                            (Extend.Alist1 Extend.Anext)),
               (fun lp p loc ->  mkAppPattern ~loc p lp ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry pattern)),
                                         (Extend.Atoken (Tok.KEYWORD "as"))),
                            (Extend.Aentry name)),
               (fun na _ p loc ->  CAst.make ~loc @@ CPatAlias (p, na) ))]);
               (Some ("1"), Some (Extend.LeftA),
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry pattern)),
                                          (Extend.Atoken (Tok.KEYWORD "%"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun key _ c loc ->
                 CAst.make ~loc @@ CPatDelimiters (key,c) ))]);
               (Some ("0"), None,
               [Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry string)),
                (fun s loc ->  CAst.make ~loc @@ CPatPrim (String s) ));
               Extend.Rule
               (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.INT ""))),
               (fun n loc ->  CAst.make ~loc @@ CPatPrim (Numeral (n,true)) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                   (Extend.Stop,
                                                                   (Extend.Atoken (Tok.KEYWORD "("))),
                                                                   (Extend.Aentryl (pattern, "200"))),
                                                      (Extend.Atoken (Tok.KEYWORD ":"))),
                                         (Extend.Aentry lconstr)),
                            (Extend.Atoken (Tok.KEYWORD ")"))),
               (fun _ ty _ p _ loc ->
                let p =
            match p with
            | { CAst.v = CPatPrim (Numeral (n,true)) } ->
                 CAst.make ~loc @@ CPatNotation((InConstrEntrySomeLevel,"( _ )"),([p],[]),[])
            | _ -> p
          in
	  CAst.make ~loc @@ CPatCast (p, ty) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Atoken (Tok.KEYWORD "("))),
                                         (Extend.Aentryl (pattern, "200"))),
                            (Extend.Atoken (Tok.KEYWORD ")"))),
               (fun _ p _ loc ->
                (match p.CAst.v with
            | CPatPrim (Numeral (n,true)) ->
                 CAst.make ~loc @@ CPatNotation((InConstrEntrySomeLevel,"( _ )"),([p],[]),[])
            | _ -> p) ));
               Extend.Rule
               (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "_"))),
               (fun _ loc ->  CAst.make ~loc @@ CPatAtom None ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Atoken (Tok.KEYWORD "{|"))),
                                         (Extend.Aentry record_patterns)),
                            (Extend.Atoken (Tok.KEYWORD "|}"))),
               (fun _ pat _ loc ->  CAst.make ~loc @@ CPatRecord pat ));
               Extend.Rule
               (Extend.Next (Extend.Stop, (Extend.Aentry Prim.reference)),
               (fun r loc ->  CAst.make ~loc @@ CPatAtom (Some r) ))])])
        in let () =
        Gram.gram_extend impl_ident_tail
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD ":"))),
                                           (Extend.Aentry lconstr)),
                              (Extend.Atoken (Tok.KEYWORD "}"))),
                 (fun _ c _ loc ->
                  (fun na -> CLocalAssum ([na],Default Implicit,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Alist1 (Extend.Aentry name))),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ nal loc ->
                 (fun na -> CLocalAssum (na::nal,Default Implicit,
                                CAst.make ?loc:(Loc.merge_opt na.CAst.loc (Some loc)) @@
                                CHole (Some (Evar_kinds.BinderType na.CAst.v), IntroAnonymous, None))) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Alist1 (Extend.Aentry name))),
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ c _ nal loc ->
                 (fun na -> CLocalAssum (na::nal,Default Implicit,c)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ loc ->  binder_of_name Implicit ))])])
        in let () =
        Gram.gram_extend fixannot
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "{"))),
                                                        (Extend.Atoken (Tok.IDENT "measure"))),
                                                        (Extend.Aentry constr)),
                                                        (Extend.Aopt (Extend.Aentry identref))),
                                           (Extend.Aopt (Extend.Aentry constr))),
                              (Extend.Atoken (Tok.KEYWORD "}"))),
                 (fun _ rel id m _ _ loc ->  (id, CMeasureRec (m,rel)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "{"))),
                                                                    (Extend.Atoken (Tok.IDENT "wf"))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Aopt (Extend.Aentry identref))),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ id rel _ _ loc ->  (id, CWfRec rel) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "{"))),
                                                       (Extend.Atoken (Tok.IDENT "struct"))),
                                          (Extend.Aentry identref)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ id _ _ loc ->  (Some id, CStructRec) ))])])
        in let () =
        Gram.gram_extend impl_name_head
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry impl_ident_head)),
                 (fun id loc ->  CAst.make ~loc @@ Name id ))])])
        in let () =
        Gram.gram_extend binders_fixannot
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->  [], (None, CStructRec) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry binder)),
                             (Extend.Aentry binders_fixannot)),
                (fun bl b loc ->  b @ fst bl, snd bl ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry fixannot)),
                (fun f loc ->  [], f ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry impl_name_head)),
                                          (Extend.Aentry impl_ident_tail)),
                             (Extend.Aentry binders_fixannot)),
                (fun bl assum na loc ->  (assum na :: fst bl), snd bl ))])])
        in let () =
        Gram.gram_extend open_binders
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry closed_binder)),
                              (Extend.Aentry binders)),
                 (fun bl' bl loc ->  bl@bl' ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry name)),
                                          (Extend.Atoken (Tok.KEYWORD ".."))),
                             (Extend.Aentry name)),
                (fun id2 _ id1 loc ->
                 [CLocalAssum ([id1;(CAst.make ~loc (Name ldots_var));id2],
	                  Default Explicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry name)),
                                          (Extend.Alist0 (Extend.Aentry name))),
                             (Extend.Aentry binders)),
                (fun bl idl id loc ->  binders_of_names (id::idl) @ bl ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Aentry name)),
                                                       (Extend.Alist0 (Extend.Aentry name))),
                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                             (Extend.Aentry lconstr)),
                (fun c _ idl id loc ->
                 [CLocalAssum (id::idl,Default Explicit,c)]
	(* binders factorized with open binder *) ))])])
        in let () =
        Gram.gram_extend binders
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist0 (Extend.Aentry binder))),
                 (fun l loc ->  List.flatten l ))])])
        in let () =
        Gram.gram_extend binder
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry closed_binder)),
                 (fun bl loc ->  bl ));
                Extend.Rule (Extend.Next (Extend.Stop, (Extend.Aentry name)),
                (fun id loc ->
                 [CLocalAssum ([id],Default Explicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))] ))])])
        in let () =
        Gram.gram_extend closed_binder
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "'"))),
                              (Extend.Aentryl (pattern, "0"))),
                 (fun p _ loc ->
                  let (p, ty) =
            match p.CAst.v with
            | CPatCast (p, ty) -> (p, Some ty)
            | _ -> (p, None)
          in
          [CLocalPattern (CAst.make ~loc (p, ty))] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "`{"))),
                                          (Extend.Alist1sep ((Extend.Aentry typeclass_constraint), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ tc _ loc ->
                 List.map (fun (n, b, t) -> CLocalAssum ([n], Generalized (Implicit, Implicit, b), t)) tc ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "`("))),
                                          (Extend.Alist1sep ((Extend.Aentry typeclass_constraint), (Extend.Atoken (Tok.KEYWORD ","))))),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ tc _ loc ->
                 List.map (fun (n, b, t) -> CLocalAssum ([n], Generalized (Implicit, Explicit, b), t)) tc ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "{"))),
                                                       (Extend.Aentry name)),
                                          (Extend.Alist1 (Extend.Aentry name))),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ idl id _ loc ->
                 List.map (fun id -> CLocalAssum ([id],Default Implicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))) (id::idl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "{"))),
                                                                    (Extend.Aentry name)),
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ c _ id _ loc ->
                 [CLocalAssum ([id],Default Implicit,c)] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "{"))),
                                                                    (Extend.Aentry name)),
                                                                    (Extend.Alist1 (Extend.Aentry name))),
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ c _ idl id _ loc ->
                 [CLocalAssum (id::idl,Default Implicit,c)] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "{"))),
                                          (Extend.Aentry name)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ id _ loc ->
                 [CLocalAssum ([id],Default Implicit, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry name)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                                    (Extend.Aentry lconstr)),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ t _ id _ loc ->  [CLocalDef (id,c,Some t)] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry name)),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ id _ loc ->
                 (match c.CAst.v with
          | CCast(c, CastConv t) -> [CLocalDef (id,c,Some t)]
          | _ -> [CLocalDef (id,c,None)]) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry name)),
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ id _ loc ->
                 [CLocalAssum ([id],Default Explicit,c)] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                                    (Extend.Aentry name)),
                                                                    (Extend.Alist1 (Extend.Aentry name))),
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ c _ idl id _ loc ->
                 [CLocalAssum (id::idl,Default Explicit,c)] ))])])
        in let () =
        Gram.gram_extend typeclass_constraint
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentryl (operconstr, "200"))),
                 (fun c loc ->  (CAst.make ~loc Anonymous), false, c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry name_colon)),
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Stop },
                                                         (fun loc ->
                                                          false ));
                                                         Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "!"))) },
                                                         (fun _ loc ->
                                                          true ))])),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c expl iid loc ->  (CAst.make ~loc iid), expl, c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "{"))),
                                                                    (Extend.Aentry name)),
                                                                    (Extend.Atoken (Tok.KEYWORD "}"))),
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Stop },
                                                         (fun loc ->
                                                          false ));
                                                         Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "!"))) },
                                                         (fun _ loc ->
                                                          true ))])),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c expl _ _ id _ loc ->  id, expl, c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "!"))),
                             (Extend.Aentryl (operconstr, "200"))),
                (fun c _ loc ->  (CAst.make ~loc Anonymous), true, c ))])])
        in let () =
        Gram.gram_extend type_cstr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                                                          (Extend.Aentry lconstr)) },
                                                          (fun c _ loc ->
                                                           c ))]))),
                 (fun c loc ->  Loc.tag ~loc c ))])])
        in ()


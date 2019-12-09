

open Pp
open CErrors
open Util
open Names
open Glob_term
open Vernacexpr
open Constrexpr
open Constrexpr_ops
open Extend
open Decl_kinds
open Declaremods
open Declarations
open Namegen
open Tok (* necessary for camlp5 *)

open Pcoq
open Pcoq.Prim
open Pcoq.Constr
open Pcoq.Module
open Pvernac.Vernac_

let vernac_kw = [ ";"; ","; ">->"; ":<"; "<:"; "where"; "at" ]
let _ = List.iter CLexer.add_keyword vernac_kw

(* Rem: do not join the different GEXTEND into one, it breaks native *)
(* compilation on PowerPC and Sun architectures *)

let query_command = Entry.create "vernac:query_command"

let subprf = Entry.create "vernac:subprf"

let class_rawexpr = Entry.create "vernac:class_rawexpr"
let thm_token = Entry.create "vernac:thm_token"
let def_body = Entry.create "vernac:def_body"
let decl_notation = Entry.create "vernac:decl_notation"
let record_field = Entry.create "vernac:record_field"
let of_type_with_opt_coercion = Entry.create "vernac:of_type_with_opt_coercion"
let instance_name = Entry.create "vernac:instance_name"
let section_subset_expr = Entry.create "vernac:section_subset_expr"

let make_bullet s =
  let open Proof_bullet in
  let n = String.length s in
  match s.[0] with
  | '-' -> Dash n
  | '+' -> Plus n
  | '*' -> Star n
  | _ -> assert false

let parse_compat_version = let open Flags in function
  | "8.9" -> Current
  | "8.8" -> V8_8
  | "8.7" -> V8_7
  | ("8.6" | "8.5" | "8.4" | "8.3" | "8.2" | "8.1" | "8.0") as s ->
    CErrors.user_err ~hdr:"get_compat_version"
      Pp.(str "Compatibility with version " ++ str s ++ str " not supported.")
  | s ->
    CErrors.user_err ~hdr:"get_compat_version"
      Pp.(str "Unknown compatibility version \"" ++ str s ++ str "\".")


let _ = let decorated_vernac = Gram.Entry.create "decorated_vernac"
        and attributes = Gram.Entry.create "attributes"
        and attribute_list = Gram.Entry.create "attribute_list"
        and attribute = Gram.Entry.create "attribute"
        and attribute_value = Gram.Entry.create "attribute_value"
        and vernac = Gram.Entry.create "vernac"
        and vernac_poly = Gram.Entry.create "vernac_poly"
        and vernac_aux = Gram.Entry.create "vernac_aux"
        and located_vernac = Gram.Entry.create "located_vernac"
        in
        let () =
        Gram.gram_extend vernac_control
        (Some
        (Extend.First), [(None, None,
                         [Extend.Rule
                          (Extend.Next (Extend.Stop,
                                       (Extend.Aentry decorated_vernac)),
                          (fun v loc ->  let (f, v) = v in VernacExpr(f, v) ));
                         Extend.Rule
                         (Extend.Next (Extend.Next (Extend.Stop,
                                                   (Extend.Atoken (Tok.IDENT "Fail"))),
                                      (Extend.Aentry vernac_control)),
                         (fun v _ loc ->  VernacFail v ));
                         Extend.Rule
                         (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                (Extend.Atoken (Tok.IDENT "Timeout"))),
                                                   (Extend.Aentry natural)),
                                      (Extend.Aentry vernac_control)),
                         (fun v n _ loc ->  VernacTimeout(n,v) ));
                         Extend.Rule
                         (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                (Extend.Atoken (Tok.IDENT "Redirect"))),
                                                   (Extend.Aentry ne_string)),
                                      (Extend.Aentry located_vernac)),
                         (fun c s _ loc ->  VernacRedirect (s, c) ));
                         Extend.Rule
                         (Extend.Next (Extend.Next (Extend.Stop,
                                                   (Extend.Atoken (Tok.IDENT "Time"))),
                                      (Extend.Aentry located_vernac)),
                         (fun c _ loc ->  VernacTime (false,c) ))])])
        in let () =
        Gram.gram_extend decorated_vernac
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry vernac)),
                 (fun fv loc ->  fv ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry attributes)),
                             (Extend.Aentry vernac)),
                (fun fv a loc ->  let (f, v) = fv in (List.append a f, v) ))])])
        in let () =
        Gram.gram_extend attributes
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "#["))),
                                           (Extend.Aentry attribute_list)),
                              (Extend.Atoken (Tok.KEYWORD "]"))),
                 (fun _ a _ loc ->  a ))])])
        in let () =
        Gram.gram_extend attribute_list
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist0sep ((Extend.Aentry attribute), (Extend.Atoken (Tok.KEYWORD ","))))),
                 (fun a loc ->  a ))])])
        in let () =
        Gram.gram_extend attribute
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry ident)),
                              (Extend.Aentry attribute_value)),
                 (fun v k loc ->  Names.Id.to_string k, v ))])])
        in let () =
        Gram.gram_extend attribute_value
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  VernacFlagEmpty ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "("))),
                                          (Extend.Aentry attribute_list)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ a _ loc ->  VernacFlagList a ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "="))),
                             (Extend.Aentry string)),
                (fun v _ loc ->  VernacFlagLeaf v ))])])
        in let () =
        Gram.gram_extend vernac
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry vernac_poly)),
                 (fun v loc ->  v ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Global"))),
                             (Extend.Aentry vernac_poly)),
                (fun v _ loc ->
                 let (f, v) = v in (("global", VernacFlagEmpty) :: f, v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Local"))),
                             (Extend.Aentry vernac_poly)),
                (fun v _ loc ->
                 let (f, v) = v in (("local", VernacFlagEmpty) :: f, v) ))])])
        in let () =
        Gram.gram_extend vernac_poly
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry vernac_aux)),
                 (fun v loc ->  v ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Monomorphic"))),
                             (Extend.Aentry vernac_aux)),
                (fun v _ loc ->
                 let (f, v) = v in (("monomorphic", VernacFlagEmpty) :: f, v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Polymorphic"))),
                             (Extend.Aentry vernac_aux)),
                (fun v _ loc ->
                 let (f, v) = v in (("polymorphic", VernacFlagEmpty) :: f, v) ))])])
        in let () =
        Gram.gram_extend vernac_aux
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry subprf)),
                 (fun c loc ->  ([], c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry syntax)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ c loc ->  ([], c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry command)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ c loc ->  ([], c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry gallina_ext)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ g loc ->  ([], g) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry gallina)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ g loc ->  ([], g) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Program"))),
                                          (Extend.Aentry gallina_ext)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ g _ loc ->  (["program", VernacFlagEmpty], g) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Program"))),
                                          (Extend.Aentry gallina)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ g _ loc ->  (["program", VernacFlagEmpty], g) ))])])
        in let () =
        Gram.gram_extend vernac_aux
        (Some
        (Extend.Last), [(None, None,
                        [Extend.Rule
                         (Extend.Next (Extend.Stop,
                                      (Extend.Aentry command_entry)),
                         (fun prfcom loc ->  ([], prfcom) ))])])
        in let () =
        Gram.gram_extend noedit_mode
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry query_command)),
                 (fun c loc ->  c None ))])])
        in let () =
        Gram.gram_extend subprf
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.KEYWORD "}"))),
                 (fun _ loc ->  VernacEndSubproof ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "{"))),
                (fun _ loc ->  VernacSubproof None ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.BULLET ""))),
                (fun s loc ->  VernacBullet (make_bullet s) ))])])
        in let () =
        Gram.gram_extend located_vernac
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry vernac_control)),
                 (fun v loc ->  CAst.make ~loc v ))])])
        in ()



let warn_plural_command =
  CWarnings.create ~name:"plural-command" ~category:"pedantic" ~default:CWarnings.Disabled
         (fun kwd -> strbrk (Printf.sprintf "Command \"%s\" expects more than one assumption." kwd))

let test_plural_form loc kwd = function
  | [(_,([_],_))] ->
     warn_plural_command ~loc kwd
  | _ -> ()

let test_plural_form_types loc kwd = function
  | [([_],_)] ->
     warn_plural_command ~loc kwd
  | _ -> ()

let lname_of_lident : lident -> lname =
  CAst.map (fun s -> Name s)

let name_of_ident_decl : ident_decl -> name_decl =
  on_fst lname_of_lident


let _ = let def_token = Gram.Entry.create "def_token"
        and assumption_token = Gram.Entry.create "assumption_token"
        and assumptions_token = Gram.Entry.create "assumptions_token"
        and inline = Gram.Entry.create "inline"
        and univ_constraint = Gram.Entry.create "univ_constraint"
        and finite_token = Gram.Entry.create "finite_token"
        and cumulativity_token = Gram.Entry.create "cumulativity_token"
        and private_token = Gram.Entry.create "private_token"
        and reduce = Gram.Entry.create "reduce"
        and one_decl_notation = Gram.Entry.create "one_decl_notation"
        and decl_sep = Gram.Entry.create "decl_sep"
        and opt_constructors_or_fields =
          Gram.Entry.create "opt_constructors_or_fields"
        and inductive_definition = Gram.Entry.create "inductive_definition"
        and constructor_list_or_record_decl =
          Gram.Entry.create "constructor_list_or_record_decl"
        and opt_coercion = Gram.Entry.create "opt_coercion"
        and corec_definition = Gram.Entry.create "corec_definition"
        and type_cstr = Gram.Entry.create "type_cstr"
        and scheme = Gram.Entry.create "scheme"
        and scheme_kind = Gram.Entry.create "scheme_kind"
        and record_fields = Gram.Entry.create "record_fields"
        and record_binder_body = Gram.Entry.create "record_binder_body"
        and record_binder = Gram.Entry.create "record_binder"
        and assum_list = Gram.Entry.create "assum_list"
        and assum_coe = Gram.Entry.create "assum_coe"
        and simple_assum_coe = Gram.Entry.create "simple_assum_coe"
        and constructor_type = Gram.Entry.create "constructor_type"
        and constructor = Gram.Entry.create "constructor"
        in
        let () =
        Gram.gram_extend gallina
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT "Constraint"))),
                              (Extend.Alist1sep ((Extend.Aentry univ_constraint), (Extend.Atoken (Tok.KEYWORD ","))))),
                 (fun l _ loc ->  VernacConstraint l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Universes"))),
                             (Extend.Alist1 (Extend.Aentry identref))),
                (fun l _ loc ->  VernacUniverse l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Universe"))),
                             (Extend.Alist1 (Extend.Aentry identref))),
                (fun l _ loc ->  VernacUniverse l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Register"))),
                                          (Extend.Atoken (Tok.IDENT "Inline"))),
                             (Extend.Aentry identref)),
                (fun id _ _ loc ->  VernacRegister(id, RegisterInline) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Combined"))),
                                                                    (Extend.Atoken (Tok.IDENT "Scheme"))),
                                                       (Extend.Aentry identref)),
                                          (Extend.Atoken (Tok.IDENT "from"))),
                             (Extend.Alist1sep ((Extend.Aentry identref), (Extend.Atoken (Tok.KEYWORD ","))))),
                (fun l _ id _ _ loc ->  VernacCombinedScheme (id, l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Scheme"))),
                             (Extend.Alist1sep ((Extend.Aentry scheme), (Extend.Atoken (Tok.KEYWORD "with"))))),
                (fun l _ loc ->  VernacScheme l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Let"))),
                                          (Extend.Atoken (Tok.KEYWORD "CoFixpoint"))),
                             (Extend.Alist1sep ((Extend.Aentry corec_definition), (Extend.Atoken (Tok.KEYWORD "with"))))),
                (fun corecs _ _ loc ->
                 VernacCoFixpoint (DoDischarge, corecs) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "CoFixpoint"))),
                             (Extend.Alist1sep ((Extend.Aentry corec_definition), (Extend.Atoken (Tok.KEYWORD "with"))))),
                (fun corecs _ loc ->
                 VernacCoFixpoint (NoDischarge, corecs) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Let"))),
                                          (Extend.Atoken (Tok.KEYWORD "Fixpoint"))),
                             (Extend.Alist1sep ((Extend.Aentry rec_definition), (Extend.Atoken (Tok.KEYWORD "with"))))),
                (fun recs _ _ loc ->  VernacFixpoint (DoDischarge, recs) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "Fixpoint"))),
                             (Extend.Alist1sep ((Extend.Aentry rec_definition), (Extend.Atoken (Tok.KEYWORD "with"))))),
                (fun recs _ loc ->  VernacFixpoint (NoDischarge, recs) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Aopt (Extend.Aentry cumulativity_token))),
                                                       (Extend.Aentry private_token)),
                                          (Extend.Aentry finite_token)),
                             (Extend.Alist1sep ((Extend.Aentry inductive_definition), (Extend.Atoken (Tok.KEYWORD "with"))))),
                (fun indl f priv cum loc ->
                 let (k,f) = f in
          let indl=List.map (fun ((a,b,c,d),e) -> ((a,b,c,k,d),e)) indl in
          VernacInductive (cum, priv,f,indl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Let"))),
                                          (Extend.Aentry identref)),
                             (Extend.Aentry def_body)),
                (fun b id _ loc ->
                 VernacDefinition ((DoDischarge, Let), (lname_of_lident id, None), b) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry def_token)),
                                          (Extend.Aentry ident_decl)),
                             (Extend.Aentry def_body)),
                (fun b id d loc ->
                 VernacDefinition (d, name_of_ident_decl id, b) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry assumptions_token)),
                                          (Extend.Aentry inline)),
                             (Extend.Aentry assum_list)),
                (fun bl nl tk loc ->
                 let (kwd,stre) = tk in 
            test_plural_form loc kwd bl;
            VernacAssumption (stre, nl, bl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry assumption_token)),
                                          (Extend.Aentry inline)),
                             (Extend.Aentry assum_list)),
                (fun bl nl stre loc ->  VernacAssumption (stre, nl, bl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Aentry thm_token)),
                                                                    (Extend.Aentry ident_decl)),
                                                                    (Extend.Aentry binders)),
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Alist0 (Extend.Arules [Extend.Rules 
                                                           ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Atoken (Tok.KEYWORD "with"))),
                                                           (Extend.Aentry ident_decl)),
                                                           (Extend.Aentry binders)),
                                                           (Extend.Atoken (Tok.KEYWORD ":"))),
                                                           (Extend.Aentry lconstr)) },
                                                           (fun c _ bl id _
                                                           loc ->
                                                            (id,(bl,c)) ))]))),
                (fun l c _ bl id thm loc ->
                 VernacStartTheoremProof (thm, (id,(bl,c))::l) ))])])
        in let () =
        Gram.gram_extend thm_token
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "Property"))),
                 (fun _ loc ->  Property ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Proposition"))),
                (fun _ loc ->  Proposition ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Corollary"))),
                (fun _ loc ->  Corollary ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Remark"))),
                (fun _ loc ->  Remark ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Fact"))),
                (fun _ loc ->  Fact ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Lemma"))),
                (fun _ loc ->  Lemma ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Theorem"))),
                (fun _ loc ->  Theorem ))])])
        in let () =
        Gram.gram_extend def_token
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "SubClass"))),
                 (fun _ loc ->  (NoDischarge,SubClass) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Example"))),
                (fun _ loc ->  (NoDischarge,Example) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Definition"))),
                (fun _ loc ->  (NoDischarge,Definition) ))])])
        in let () =
        Gram.gram_extend assumption_token
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "Conjecture"))),
                 (fun _ loc ->  (NoDischarge, Conjectural) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Parameter"))),
                (fun _ loc ->  (NoDischarge, Definitional) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Axiom"))),
                (fun _ loc ->  (NoDischarge, Logical) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Variable"))),
                (fun _ loc ->  (DoDischarge, Definitional) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Hypothesis"))),
                (fun _ loc ->  (DoDischarge, Logical) ))])])
        in let () =
        Gram.gram_extend assumptions_token
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "Conjectures"))),
                 (fun _ loc ->  ("Conjectures", (NoDischarge, Conjectural)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Parameters"))),
                (fun _ loc ->  ("Parameters", (NoDischarge, Definitional)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Axioms"))),
                (fun _ loc ->  ("Axioms", (NoDischarge, Logical)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Variables"))),
                (fun _ loc ->  ("Variables", (DoDischarge, Definitional)) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Hypotheses"))),
                (fun _ loc ->  ("Hypotheses", (DoDischarge, Logical)) ))])])
        in let () =
        Gram.gram_extend inline
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  NoInline ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Inline"))),
                (fun _ loc ->  DefaultInline ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Inline"))),
                                                       (Extend.Atoken (Tok.KEYWORD "("))),
                                          (Extend.Atoken (Tok.INT ""))),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ i _ _ loc ->  InlineAt (int_of_string i) ))])])
        in let () =
        Gram.gram_extend univ_constraint
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry universe_level)),
                                           (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "<="))) },
                                                          (fun _ loc ->
                                                           Univ.Le ));
                                                          Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "="))) },
                                                          (fun _ loc ->
                                                           Univ.Eq ));
                                                          Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "<"))) },
                                                          (fun _ loc ->
                                                           Univ.Lt ))])),
                              (Extend.Aentry universe_level)),
                 (fun r ord l loc ->  (l, ord, r) ))])])
        in let () =
        Gram.gram_extend univ_decl
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "@{"))),
                                                        (Extend.Alist0 (Extend.Aentry identref))),
                                           (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Stop },
                                                          (fun loc ->
                                                           false ));
                                                          Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "+"))) },
                                                          (fun _ loc ->
                                                           true ))])),
                              (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Arules 
                                                           [Extend.Rules 
                                                           ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Atoken (Tok.KEYWORD "|}"))) },
                                                           (fun _ loc ->
                                                            false ));
                                                           Extend.Rules 
                                                           ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Atoken (Tok.KEYWORD "}"))) },
                                                           (fun _ loc ->
                                                            true ))])) },
                                                           (fun ext loc ->
                                                            ([], ext) ));
                                             Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "|"))),
                                                          (Extend.Alist0sep ((Extend.Aentry univ_constraint), (Extend.Atoken (Tok.KEYWORD ","))))),
                                                          (Extend.Arules 
                                                          [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Stop },
                                                          (fun loc ->
                                                           false ));
                                                          Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "+"))) },
                                                          (fun _ loc ->
                                                           true ))])),
                                                          (Extend.Atoken (Tok.KEYWORD "}"))) },
                                                          (fun _ ext l' _
                                                          loc ->  (l',ext) ))])),
                 (fun cs ext l _ loc ->
                  let open UState in
         { univdecl_instance = l;
           univdecl_extensible_instance = ext;
           univdecl_constraints = fst cs;
           univdecl_extensible_constraints = snd cs } ))])])
        in let () =
        Gram.gram_extend ident_decl
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry identref)),
                              (Extend.Aopt (Extend.Aentry univ_decl))),
                 (fun l i loc ->  (i, l) ))])])
        in let () =
        Gram.gram_extend finite_token
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "Class"))),
                 (fun _ loc ->  (Class true,BiFinite) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Structure"))),
                (fun _ loc ->  (Structure,BiFinite) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Record"))),
                (fun _ loc ->  (Record,BiFinite) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Variant"))),
                (fun _ loc ->  (Variant,BiFinite) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "CoInductive"))),
                (fun _ loc ->  (CoInductive,CoFinite) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Inductive"))),
                (fun _ loc ->  (Inductive_kw,Finite) ))])])
        in let () =
        Gram.gram_extend cumulativity_token
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "NonCumulative"))),
                 (fun _ loc ->  VernacNonCumulative ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Cumulative"))),
                (fun _ loc ->  VernacCumulative ))])])
        in let () =
        Gram.gram_extend private_token
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  false ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Private"))),
                (fun _ loc ->  true ))])])
        in let () =
        Gram.gram_extend def_body
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry binders)),
                                           (Extend.Atoken (Tok.KEYWORD ":"))),
                              (Extend.Aentry lconstr)),
                 (fun t _ bl loc ->  ProveBody (bl, t) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Aentry binders)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                                    (Extend.Aentry lconstr)),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry reduce)),
                             (Extend.Aentry lconstr)),
                (fun c red _ t _ bl loc ->
                 let ((bl, c), tyo) =
          if List.exists (function CLocalPattern _ -> true | _ -> false) bl
          then
            (* FIXME: "red" will be applied to types in bl and Cast with remain *)
            let c = CAst.make ~loc @@ CCast (c, CastConv t) in
            (([],mkCLambdaN ~loc bl c), None)
          else ((bl, c), Some t)
        in
	DefineBody (bl, red, c, tyo) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Aentry binders)),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry reduce)),
                             (Extend.Aentry lconstr)),
                (fun c red _ bl loc ->
                 if List.exists (function CLocalPattern _ -> true | _ -> false) bl
      then
        (* FIXME: "red" will be applied to types in bl and Cast with remain *)
        let c = mkCLambdaN ~loc bl c in
	DefineBody ([], red, c, None)
      else
        (match c with
        | { CAst.v = CCast(c, CastConv t) } -> DefineBody (bl, red, c, Some t)
        | _ -> DefineBody (bl, red, c, None)) ))])])
        in let () =
        Gram.gram_extend reduce
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Eval"))),
                                          (Extend.Aentry red_expr)),
                             (Extend.Atoken (Tok.KEYWORD "in"))),
                (fun _ r _ loc ->  Some r ))])])
        in let () =
        Gram.gram_extend one_decl_notation
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry ne_lstring)),
                                                        (Extend.Atoken (Tok.KEYWORD ":="))),
                                           (Extend.Aentry constr)),
                              (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                                                          (Extend.Atoken (Tok.IDENT ""))) },
                                                          (fun sc _ loc ->
                                                           sc ))]))),
                 (fun scopt c _ ntn loc ->  (ntn,c,scopt) ))])])
        in let () =
        Gram.gram_extend decl_sep
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "and"))),
                 (fun _ loc ->  () ))])])
        in let () =
        Gram.gram_extend decl_notation
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "where"))),
                             (Extend.Alist1sep ((Extend.Aentry one_decl_notation), (Extend.Aentry decl_sep)))),
                (fun l _ loc ->  l ))])])
        in let () =
        Gram.gram_extend opt_constructors_or_fields
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->  RecordDecl (None, []) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD ":="))),
                             (Extend.Aentry constructor_list_or_record_decl)),
                (fun lc _ loc ->  lc ))])])
        in let () =
        Gram.gram_extend inductive_definition
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry opt_coercion)),
                                                        (Extend.Aentry ident_decl)),
                                                        (Extend.Aentry binders)),
                                                        (Extend.Aopt (Extend.Arules 
                                                        [Extend.Rules 
                                                        ({ Extend.norec_rule = Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD ":"))),
                                                        (Extend.Aentry lconstr)) },
                                                        (fun c _ loc -> 
                                                         c ))]))),
                                           (Extend.Aentry opt_constructors_or_fields)),
                              (Extend.Aentry decl_notation)),
                 (fun ntn lc c indpar id oc loc ->
                  (((oc,id),indpar,c,lc),ntn) ))])])
        in let () =
        Gram.gram_extend constructor_list_or_record_decl
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  Constructors [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "{"))),
                                          (Extend.Aentry record_fields)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ fs _ loc ->  RecordDecl (None,fs) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Aentry identref)),
                                                       (Extend.Atoken (Tok.KEYWORD "{"))),
                                          (Extend.Aentry record_fields)),
                             (Extend.Atoken (Tok.KEYWORD "}"))),
                (fun _ fs _ cstr loc ->  RecordDecl (Some cstr,fs) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry identref)),
                             (Extend.Aentry constructor_type)),
                (fun c id loc ->  Constructors [ c id ] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Aentry identref)),
                                                       (Extend.Aentry constructor_type)),
                                          (Extend.Atoken (Tok.KEYWORD "|"))),
                             (Extend.Alist0sep ((Extend.Aentry constructor), (Extend.Atoken (Tok.KEYWORD "|"))))),
                (fun l _ c id loc ->  Constructors ((c id)::l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "|"))),
                             (Extend.Alist1sep ((Extend.Aentry constructor), (Extend.Atoken (Tok.KEYWORD "|"))))),
                (fun l _ loc ->  Constructors l ))])])
        in let () =
        Gram.gram_extend opt_coercion
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  false ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD ">"))),
                (fun _ loc ->  true ))])])
        in let () =
        Gram.gram_extend rec_definition
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry ident_decl)),
                                                        (Extend.Aentry binders_fixannot)),
                                                        (Extend.Aentry type_cstr)),
                                           (Extend.Aopt (Extend.Arules 
                                           [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD ":="))),
                                                         (Extend.Aentry lconstr)) },
                                                         (fun def _ loc ->
                                                          def ))]))),
                              (Extend.Aentry decl_notation)),
                 (fun ntn def ty bl id loc ->
                  let bl, annot = bl in ((id,annot,bl,ty,def),ntn) ))])])
        in let () =
        Gram.gram_extend corec_definition
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Aentry ident_decl)),
                                                        (Extend.Aentry binders)),
                                                        (Extend.Aentry type_cstr)),
                                           (Extend.Aopt (Extend.Arules 
                                           [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD ":="))),
                                                         (Extend.Aentry lconstr)) },
                                                         (fun def _ loc ->
                                                          def ))]))),
                              (Extend.Aentry decl_notation)),
                 (fun ntn def ty bl id loc ->  ((id,bl,ty,def),ntn) ))])])
        in let () =
        Gram.gram_extend type_cstr
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->
                  CAst.make ~loc @@ CHole (None, IntroAnonymous, None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                             (Extend.Aentry lconstr)),
                (fun c _ loc ->  c ))])])
        in let () =
        Gram.gram_extend scheme
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry identref)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentry scheme_kind)),
                 (fun kind _ id loc ->  (Some id,kind) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry scheme_kind)),
                (fun kind loc ->  (None,kind) ))])])
        in let () =
        Gram.gram_extend scheme_kind
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Equality"))),
                                           (Extend.Atoken (Tok.KEYWORD "for"))),
                              (Extend.Aentry smart_global)),
                 (fun ind _ _ loc ->  EqualityScheme(ind) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Case"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "for"))),
                                                       (Extend.Aentry smart_global)),
                                          (Extend.Atoken (Tok.IDENT "Sort"))),
                             (Extend.Aentry sort_family)),
                (fun s _ ind _ _ loc ->  CaseScheme(false,ind,s) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Elimination"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "for"))),
                                                       (Extend.Aentry smart_global)),
                                          (Extend.Atoken (Tok.IDENT "Sort"))),
                             (Extend.Aentry sort_family)),
                (fun s _ ind _ _ loc ->  CaseScheme(true,ind,s) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Minimality"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "for"))),
                                                       (Extend.Aentry smart_global)),
                                          (Extend.Atoken (Tok.IDENT "Sort"))),
                             (Extend.Aentry sort_family)),
                (fun s _ ind _ _ loc ->  InductionScheme(false,ind,s) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Induction"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "for"))),
                                                       (Extend.Aentry smart_global)),
                                          (Extend.Atoken (Tok.IDENT "Sort"))),
                             (Extend.Aentry sort_family)),
                (fun s _ ind _ _ loc ->  InductionScheme(true,ind,s) ))])])
        in let () =
        Gram.gram_extend record_field
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry record_binder)),
                                           (Extend.Aopt (Extend.Arules 
                                           [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "|"))),
                                                         (Extend.Aentry natural)) },
                                                         (fun n _ loc ->
                                                          n ))]))),
                              (Extend.Aentry decl_notation)),
                 (fun ntn pri bd loc ->  (bd,pri),ntn ))])])
        in let () =
        Gram.gram_extend record_fields
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry record_field)),
                (fun f loc ->  [f] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry record_field)),
                             (Extend.Atoken (Tok.KEYWORD ";"))),
                (fun _ f loc ->  [f] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry record_field)),
                                          (Extend.Atoken (Tok.KEYWORD ";"))),
                             (Extend.Aentry record_fields)),
                (fun fs _ f loc ->  f :: fs ))])])
        in let () =
        Gram.gram_extend record_binder_body
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry binders)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentry lconstr)),
                 (fun b _ l loc ->
                  fun id ->
         match b.CAst.v with
	 | CCast(b', (CastConv t|CastVM t|CastNative t)) ->
	     (None,DefExpr(id,mkCLambdaN ~loc l b',Some (mkCProdN ~loc l t)))
         | _ ->
	     (None,DefExpr(id,mkCLambdaN ~loc l b,None)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Aentry binders)),
                                                                    (Extend.Aentry of_type_with_opt_coercion)),
                                                       (Extend.Aentry lconstr)),
                                          (Extend.Atoken (Tok.KEYWORD ":="))),
                             (Extend.Aentry lconstr)),
                (fun b _ t oc l loc ->
                 fun id ->
	   (oc,DefExpr (id,mkCLambdaN ~loc l b,Some (mkCProdN ~loc l t))) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry binders)),
                                          (Extend.Aentry of_type_with_opt_coercion)),
                             (Extend.Aentry lconstr)),
                (fun t oc l loc ->
                 fun id -> (oc,AssumExpr (id,mkCProdN ~loc l t)) ))])])
        in let () =
        Gram.gram_extend record_binder
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry name)),
                              (Extend.Aentry record_binder_body)),
                 (fun f id loc ->  f id ));
                Extend.Rule (Extend.Next (Extend.Stop, (Extend.Aentry name)),
                (fun id loc ->
                 (None,AssumExpr(id, CAst.make ~loc @@ CHole (None, IntroAnonymous, None))) ))])])
        in let () =
        Gram.gram_extend assum_list
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry simple_assum_coe)),
                 (fun b loc ->  [b] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Alist1 (Extend.Aentry assum_coe))),
                (fun bl loc ->  bl ))])])
        in let () =
        Gram.gram_extend assum_coe
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                           (Extend.Aentry simple_assum_coe)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ a _ loc ->  a ))])])
        in let () =
        Gram.gram_extend simple_assum_coe
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Alist1 (Extend.Aentry ident_decl))),
                                           (Extend.Aentry of_type_with_opt_coercion)),
                              (Extend.Aentry lconstr)),
                 (fun c oc idl loc ->  (not (Option.is_empty oc),(idl,c)) ))])])
        in let () =
        Gram.gram_extend constructor_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry binders)),
                              (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Stop },
                                                           (fun loc ->
                                                            fun l id -> (false,(id,mkCProdN ~loc l (CAst.make ~loc @@ CHole (None, IntroAnonymous, None)))) ));
                                             Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Aentry of_type_with_opt_coercion)),
                                                          (Extend.Aentry lconstr)) },
                                                          (fun c coe loc ->
                                                           fun l id -> (not (Option.is_empty coe),(id,mkCProdN ~loc l c)) ))])),
                 (fun t l loc ->  t l ))])])
        in let () =
        Gram.gram_extend constructor
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry identref)),
                              (Extend.Aentry constructor_type)),
                 (fun c id loc ->  c id ))])])
        in let () =
        Gram.gram_extend of_type_with_opt_coercion
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.KEYWORD ":"))),
                 (fun _ loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                             (Extend.Atoken (Tok.KEYWORD ">"))),
                (fun _ _ loc ->  Some true ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD ":"))),
                                          (Extend.Atoken (Tok.KEYWORD ">"))),
                             (Extend.Atoken (Tok.KEYWORD ">"))),
                (fun _ _ _ loc ->  Some false ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD ":>"))),
                (fun _ loc ->  Some true ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD ":>"))),
                             (Extend.Atoken (Tok.KEYWORD ">"))),
                (fun _ _ loc ->  Some false ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD ":>>"))),
                (fun _ loc ->  Some false ))])])
        in ()



let only_starredidentrefs =
  Gram.Entry.of_parser "test_only_starredidentrefs"
    (fun strm ->
      let rec aux n =
      match Util.stream_nth n strm with
        | KEYWORD "." -> ()
        | KEYWORD ")" -> ()
        | (IDENT _ | KEYWORD "Type" | KEYWORD "*") -> aux (n+1)
        | _ -> raise Stream.Failure in
      aux 0)
let starredidentreflist_to_expr l =
  match l with
  | [] -> SsEmpty
  | x :: xs -> List.fold_right (fun i acc -> SsUnion(i,acc)) xs x

let warn_deprecated_include_type =
  CWarnings.create ~name:"deprecated-include-type" ~category:"deprecated"
         (fun () -> strbrk "Include Type is deprecated; use Include instead")


let _ = let export_token = Gram.Entry.create "export_token"
        and ext_module_type = Gram.Entry.create "ext_module_type"
        and ext_module_expr = Gram.Entry.create "ext_module_expr"
        and check_module_type = Gram.Entry.create "check_module_type"
        and check_module_types = Gram.Entry.create "check_module_types"
        and of_module_type = Gram.Entry.create "of_module_type"
        and is_module_type = Gram.Entry.create "is_module_type"
        and is_module_expr = Gram.Entry.create "is_module_expr"
        and functor_app_annot = Gram.Entry.create "functor_app_annot"
        and module_expr_inl = Gram.Entry.create "module_expr_inl"
        and module_type_inl = Gram.Entry.create "module_type_inl"
        and module_binder = Gram.Entry.create "module_binder"
        and module_expr_atom = Gram.Entry.create "module_expr_atom"
        and with_declaration = Gram.Entry.create "with_declaration"
        and starredidentref = Gram.Entry.create "starredidentref"
        and ssexpr = Gram.Entry.create "ssexpr"
        in
        let () =
        Gram.gram_extend gallina_ext
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Include"))),
                                                        (Extend.Atoken (Tok.KEYWORD "Type"))),
                                           (Extend.Aentry module_type_inl)),
                              (Extend.Alist0 (Extend.Aentry ext_module_type))),
                 (fun l e _ _ loc ->
                  warn_deprecated_include_type ~loc ();
        VernacInclude(e::l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Include"))),
                                          (Extend.Aentry module_type_inl)),
                             (Extend.Alist0 (Extend.Aentry ext_module_expr))),
                (fun l e _ loc ->  VernacInclude(e::l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Export"))),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun qidl _ loc ->  VernacImport (true,qidl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Import"))),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun qidl _ loc ->  VernacImport (false,qidl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "From"))),
                                                                    (Extend.Aentry global)),
                                                       (Extend.Atoken (Tok.IDENT "Require"))),
                                          (Extend.Aentry export_token)),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun qidl export _ ns _ loc ->
                 VernacRequire (Some ns, export, qidl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Require"))),
                                          (Extend.Aentry export_token)),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun qidl export _ loc ->
                 VernacRequire (None, export, qidl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Collection"))),
                                                       (Extend.Aentry identref)),
                                          (Extend.Atoken (Tok.KEYWORD ":="))),
                             (Extend.Aentry section_subset_expr)),
                (fun expr _ id _ loc ->  VernacNameSectionHypSet (id, expr) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "End"))),
                             (Extend.Aentry identref)),
                (fun id _ loc ->  VernacEndSegment id ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Chapter"))),
                             (Extend.Aentry identref)),
                (fun id _ loc ->  VernacBeginSection id ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Section"))),
                             (Extend.Aentry identref)),
                (fun id _ loc ->  VernacBeginSection id ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Declare"))),
                                                                    (Extend.Atoken (Tok.IDENT "Module"))),
                                                                    (Extend.Aentry export_token)),
                                                                    (Extend.Aentry identref)),
                                                       (Extend.Alist0 (Extend.Aentry module_binder))),
                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                             (Extend.Aentry module_type_inl)),
                (fun mty _ bl id export _ _ loc ->
                 VernacDeclareModule (export, id, bl, mty) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Module"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "Type"))),
                                                                    (Extend.Aentry identref)),
                                                       (Extend.Alist0 (Extend.Aentry module_binder))),
                                          (Extend.Aentry check_module_types)),
                             (Extend.Aentry is_module_type)),
                (fun body sign bl id _ _ loc ->
                 VernacDeclareModuleType (id, bl, sign, body) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Module"))),
                                                                    (Extend.Aentry export_token)),
                                                                    (Extend.Aentry identref)),
                                                       (Extend.Alist0 (Extend.Aentry module_binder))),
                                          (Extend.Aentry of_module_type)),
                             (Extend.Aentry is_module_expr)),
                (fun body sign bl id export _ loc ->
                 VernacDefineModule (export, id, bl, sign, body) ))])])
        in let () =
        Gram.gram_extend export_token
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Export"))),
                (fun _ loc ->  Some true ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Import"))),
                (fun _ loc ->  Some false ))])])
        in let () =
        Gram.gram_extend ext_module_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "<+"))),
                              (Extend.Aentry module_type_inl)),
                 (fun mty _ loc ->  mty ))])])
        in let () =
        Gram.gram_extend ext_module_expr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "<+"))),
                              (Extend.Aentry module_expr_inl)),
                 (fun mexpr _ loc ->  mexpr ))])])
        in let () =
        Gram.gram_extend check_module_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "<:"))),
                              (Extend.Aentry module_type_inl)),
                 (fun mty _ loc ->  mty ))])])
        in let () =
        Gram.gram_extend check_module_types
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist0 (Extend.Aentry check_module_type))),
                 (fun mtys loc ->  mtys ))])])
        in let () =
        Gram.gram_extend of_module_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aentry check_module_types)),
                 (fun mtys loc ->  Check mtys ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD ":"))),
                             (Extend.Aentry module_type_inl)),
                (fun mty _ loc ->  Enforce mty ))])])
        in let () =
        Gram.gram_extend is_module_type
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry module_type_inl)),
                             (Extend.Alist0 (Extend.Aentry ext_module_type))),
                (fun l mty _ loc ->  (mty::l) ))])])
        in let () =
        Gram.gram_extend is_module_expr
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  [] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry module_expr_inl)),
                             (Extend.Alist0 (Extend.Aentry ext_module_expr))),
                (fun l mexpr _ loc ->  (mexpr::l) ))])])
        in let () =
        Gram.gram_extend functor_app_annot
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  DefaultInline ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "["))),
                                                       (Extend.Atoken (Tok.IDENT "no"))),
                                          (Extend.Atoken (Tok.IDENT "inline"))),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ _ _ _ loc ->  NoInline ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "["))),
                                                                    (Extend.Atoken (Tok.IDENT "inline"))),
                                                                    (Extend.Atoken (Tok.KEYWORD "at"))),
                                                       (Extend.Atoken (Tok.IDENT "level"))),
                                          (Extend.Atoken (Tok.INT ""))),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ i _ _ _ _ loc ->  InlineAt (int_of_string i) ))])])
        in let () =
        Gram.gram_extend module_expr_inl
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry module_expr)),
                              (Extend.Aentry functor_app_annot)),
                 (fun a me loc ->  (me,a) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "!"))),
                             (Extend.Aentry module_expr)),
                (fun me _ loc ->  (me,NoInline) ))])])
        in let () =
        Gram.gram_extend module_type_inl
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry module_type)),
                              (Extend.Aentry functor_app_annot)),
                 (fun a me loc ->  (me,a) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "!"))),
                             (Extend.Aentry module_type)),
                (fun me _ loc ->  (me,NoInline) ))])])
        in let () =
        Gram.gram_extend module_binder
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                                        (Extend.Aentry export_token)),
                                                        (Extend.Alist1 (Extend.Aentry identref))),
                                                        (Extend.Atoken (Tok.KEYWORD ":"))),
                                           (Extend.Aentry module_type_inl)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ mty _ idl export _ loc ->  (export,idl,mty) ))])])
        in let () =
        Gram.gram_extend module_expr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry module_expr)),
                              (Extend.Aentry module_expr_atom)),
                 (fun me2 me1 loc ->  CAst.make ~loc @@ CMapply (me1,me2) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry module_expr_atom)),
                (fun me loc ->  me ))])])
        in let () =
        Gram.gram_extend module_expr_atom
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                           (Extend.Aentry module_expr)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ me _ loc ->  me ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry qualid)),
                (fun qid loc ->  CAst.make ~loc @@ CMident qid ))])])
        in let () =
        Gram.gram_extend with_declaration
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Module"))),
                                                        (Extend.Aentry fullyqualid)),
                                           (Extend.Atoken (Tok.KEYWORD ":="))),
                              (Extend.Aentry qualid)),
                 (fun qid _ fqid _ loc ->  CWith_Module (fqid,qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "Definition"))),
                                                                    (Extend.Aentry fullyqualid)),
                                                       (Extend.Aopt (Extend.Aentry univ_decl))),
                                          (Extend.Atoken (Tok.KEYWORD ":="))),
                             (Extend.Aentry Constr.lconstr)),
                (fun c _ udecl fqid _ loc ->
                 CWith_Definition (fqid,udecl,c) ))])])
        in let () =
        Gram.gram_extend module_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aentry module_type)),
                                           (Extend.Atoken (Tok.KEYWORD "with"))),
                              (Extend.Aentry with_declaration)),
                 (fun decl _ mty loc ->
                  CAst.make ~loc @@ CMwith (mty,decl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry module_type)),
                             (Extend.Aentry module_expr_atom)),
                (fun me mty loc ->  CAst.make ~loc @@ CMapply (mty,me) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "("))),
                                          (Extend.Aentry module_type)),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ mt _ loc ->  mt ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry qualid)),
                (fun qid loc ->  CAst.make ~loc @@ CMident qid ))])])
        in let () =
        Gram.gram_extend section_subset_expr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ssexpr)),
                 (fun e loc ->  e ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry only_starredidentrefs)),
                             (Extend.Alist0 (Extend.Aentry starredidentref))),
                (fun l _ loc ->  starredidentreflist_to_expr l ))])])
        in let () =
        Gram.gram_extend starredidentref
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "Type"))),
                              (Extend.Atoken (Tok.KEYWORD "*"))),
                 (fun _ _ loc ->  SsFwdClose SsType ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.KEYWORD "Type"))),
                (fun _ loc ->  SsType ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry identref)),
                             (Extend.Atoken (Tok.KEYWORD "*"))),
                (fun _ i loc ->  SsFwdClose(SsSingl i) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry identref)),
                (fun i loc ->  SsSingl i ))])])
        in let () =
        Gram.gram_extend ssexpr
        (None, [(Some ("35"), None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "-"))),
                              (Extend.Aentry ssexpr)),
                 (fun e _ loc ->  SsCompl e ))]);
               (Some ("50"), None,
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry ssexpr)),
                                          (Extend.Atoken (Tok.KEYWORD "+"))),
                             (Extend.Aentry ssexpr)),
                (fun e2 _ e1 loc ->  SsUnion(e1,e2) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Aentry ssexpr)),
                                         (Extend.Atoken (Tok.KEYWORD "-"))),
                            (Extend.Aentry ssexpr)),
               (fun e2 _ e1 loc ->  SsSubstr(e1,e2) ))]);
               (Some ("0"), None,
               [Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                       (Extend.Aentry ssexpr)),
                                          (Extend.Atoken (Tok.KEYWORD ")"))),
                             (Extend.Atoken (Tok.KEYWORD "*"))),
                (fun _ _ e _ loc ->  SsFwdClose e ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                      (Extend.Atoken (Tok.KEYWORD "("))),
                                         (Extend.Aentry ssexpr)),
                            (Extend.Atoken (Tok.KEYWORD ")"))),
               (fun _ e _ loc ->  e ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                   (Extend.Stop,
                                                                   (Extend.Atoken (Tok.KEYWORD "("))),
                                                                   (Extend.Aentry only_starredidentrefs)),
                                                      (Extend.Alist0 (Extend.Aentry starredidentref))),
                                         (Extend.Atoken (Tok.KEYWORD ")"))),
                            (Extend.Atoken (Tok.KEYWORD "*"))),
               (fun _ _ l _ _ loc ->
                SsFwdClose(starredidentreflist_to_expr l) ));
               Extend.Rule
               (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                   (Extend.Atoken (Tok.KEYWORD "("))),
                                                      (Extend.Aentry only_starredidentrefs)),
                                         (Extend.Alist0 (Extend.Aentry starredidentref))),
                            (Extend.Atoken (Tok.KEYWORD ")"))),
               (fun _ l _ _ loc ->  starredidentreflist_to_expr l ));
               Extend.Rule
               (Extend.Next (Extend.Stop, (Extend.Aentry starredidentref)),
               (fun i loc ->  i ))])])
        in ()

let _ = let arguments_modifier = Gram.Entry.create "arguments_modifier"
        and scope = Gram.Entry.create "scope"
        and argument_spec = Gram.Entry.create "argument_spec"
        and argument_spec_block = Gram.Entry.create "argument_spec_block"
        and more_implicits_block = Gram.Entry.create "more_implicits_block"
        and strategy_level = Gram.Entry.create "strategy_level"
        and reserv_list = Gram.Entry.create "reserv_list"
        and reserv_tuple = Gram.Entry.create "reserv_tuple"
        and simple_reserv = Gram.Entry.create "simple_reserv"
        in
        let () =
        Gram.gram_extend gallina_ext
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT "Generalizable"))),
                              (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Arules 
                                                           [Extend.Rules 
                                                           ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Atoken (Tok.IDENT "Variables"))) },
                                                           (fun _ loc ->
                                                            () ));
                                                           Extend.Rules 
                                                           ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Atoken (Tok.KEYWORD "Variable"))) },
                                                           (fun _ loc ->
                                                            () ))])),
                                                           (Extend.Alist1 (Extend.Aentry identref))) },
                                                           (fun idl _ loc ->
                                                            Some idl ));
                                             Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.IDENT "No"))),
                                                          (Extend.Atoken (Tok.IDENT "Variables"))) },
                                                          (fun _ _ loc ->
                                                           None ));
                                             Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.IDENT "All"))),
                                                          (Extend.Atoken (Tok.IDENT "Variables"))) },
                                                          (fun _ _ loc ->
                                                           Some [] ))])),
                 (fun gen _ loc ->  VernacGeneralizable gen ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Implicit"))),
                                          (Extend.Atoken (Tok.IDENT "Types"))),
                             (Extend.Aentry reserv_list)),
                (fun bl _ _ loc ->
                 test_plural_form_types loc "Implicit Types" bl;
           VernacReserve bl ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Implicit"))),
                                          (Extend.Atoken (Tok.KEYWORD "Type"))),
                             (Extend.Aentry reserv_list)),
                (fun bl _ _ loc ->  VernacReserve bl ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Arguments"))),
                                                                    (Extend.Aentry smart_global)),
                                                       (Extend.Alist0 (Extend.Aentry argument_spec_block))),
                                          (Extend.Aopt (Extend.Arules 
                                          [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD ","))),
                                                        (Extend.Alist1sep ((Extend.Arules 
                                                        [Extend.Rules 
                                                        ({ Extend.norec_rule = Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Alist0 (Extend.Aentry more_implicits_block))) },
                                                        (fun impl loc ->
                                                         List.flatten impl ))]), (Extend.Atoken (Tok.KEYWORD ","))))) },
                                                        (fun impl _ loc ->
                                                         impl ))]))),
                             (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD ":"))),
                                                         (Extend.Alist1sep ((Extend.Aentry arguments_modifier), (Extend.Atoken (Tok.KEYWORD ","))))) },
                                                         (fun l _ loc ->
                                                          l ))]))),
                (fun mods more_implicits args qid _ loc ->
                 let mods = match mods with None -> [] | Some l -> List.flatten l in
         let slash_position = ref None in
         let rec parse_args i = function
           | [] -> []
           | `Id x :: args -> x :: parse_args (i+1) args
           | `Slash :: args ->
              if Option.is_empty !slash_position then
                (slash_position := Some i; parse_args i args)
              else
                user_err Pp.(str "The \"/\" modifier can occur only once")
         in
         let args = parse_args 0 (List.flatten args) in
         let more_implicits = Option.default [] more_implicits in
         VernacArguments (qid, args, more_implicits, !slash_position, mods) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Existing"))),
                                          (Extend.Atoken (Tok.IDENT "Class"))),
                             (Extend.Aentry global)),
                (fun is _ _ loc ->  VernacDeclareClass is ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Existing"))),
                                                       (Extend.Atoken (Tok.IDENT "Instances"))),
                                          (Extend.Alist1 (Extend.Aentry global))),
                             (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "|"))),
                                                         (Extend.Aentry natural)) },
                                                         (fun i _ loc ->
                                                          i ))]))),
                (fun pri ids _ _ loc ->
                 let info = { Typeclasses.hint_priority = pri; hint_pattern = None } in
         let insts = List.map (fun i -> (i, info)) ids in
	  VernacDeclareInstances insts ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Existing"))),
                                                       (Extend.Atoken (Tok.IDENT "Instance"))),
                                          (Extend.Aentry global)),
                             (Extend.Aentry hint_info)),
                (fun info id _ _ loc ->  VernacDeclareInstances [id, info] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Instance"))),
                                                                    (Extend.Aentry instance_name)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                                    (Extend.Arules 
                                                                    [Extend.Rules 
                                                                    ({ Extend.norec_rule = Extend.Stop },
                                                                    (fun
                                                                    loc ->
                                                                     Decl_kinds.Explicit ));
                                                                    Extend.Rules 
                                                                    ({ Extend.norec_rule = Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "!"))) },
                                                                    (fun _
                                                                    loc ->
                                                                     Decl_kinds.Implicit ))])),
                                                       (Extend.Aentryl (operconstr, "200"))),
                                          (Extend.Aentry hint_info)),
                             (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Stop },
                                                          (fun loc ->
                                                           None ));
                                            Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD ":="))),
                                                         (Extend.Aentry lconstr)) },
                                                         (fun c _ loc ->
                                                          Some (false,c) ));
                                            Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD ":="))),
                                                         (Extend.Atoken (Tok.KEYWORD "{"))),
                                                         (Extend.Aentry record_declaration)),
                                                         (Extend.Atoken (Tok.KEYWORD "}"))) },
                                                         (fun _ r _ _ loc ->
                                                          Some (true,r) ))])),
                (fun props info t expl _ namesup _ loc ->
                 VernacInstance (false,snd namesup,(fst namesup,expl,t),props,info) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Context"))),
                             (Extend.Alist1 (Extend.Aentry binder))),
                (fun c _ loc ->  VernacContext (List.flatten c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Coercion"))),
                                                                    (Extend.Aentry by_notation)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Aentry class_rawexpr)),
                                          (Extend.Atoken (Tok.KEYWORD ">->"))),
                             (Extend.Aentry class_rawexpr)),
                (fun t _ s _ ntn _ loc ->
                 VernacCoercion (CAst.make ~loc @@ ByNotation ntn, s, t) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Coercion"))),
                                                                    (Extend.Aentry global)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Aentry class_rawexpr)),
                                          (Extend.Atoken (Tok.KEYWORD ">->"))),
                             (Extend.Aentry class_rawexpr)),
                (fun t _ s _ qid _ loc ->
                 VernacCoercion (CAst.make ~loc @@ AN qid, s, t) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Identity"))),
                                                                    (Extend.Atoken (Tok.IDENT "Coercion"))),
                                                                    (Extend.Aentry identref)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Aentry class_rawexpr)),
                                          (Extend.Atoken (Tok.KEYWORD ">->"))),
                             (Extend.Aentry class_rawexpr)),
                (fun t _ s _ f _ _ loc ->  VernacIdentityCoercion (f, s, t) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Coercion"))),
                                          (Extend.Aentry global)),
                             (Extend.Aentry def_body)),
                (fun d qid _ loc ->
                 let s = coerce_reference_to_id qid in
          VernacDefinition ((NoDischarge,Coercion),((CAst.make (Name s)),None),d) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Canonical"))),
                                                       (Extend.Atoken (Tok.IDENT "Structure"))),
                                          (Extend.Aentry global)),
                             (Extend.Aentry def_body)),
                (fun d qid _ _ loc ->
                 let s = coerce_reference_to_id qid in
          VernacDefinition ((NoDischarge,CanonicalStructure),((CAst.make (Name s)),None),d) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Canonical"))),
                                          (Extend.Atoken (Tok.IDENT "Structure"))),
                             (Extend.Aentry by_notation)),
                (fun ntn _ _ loc ->
                 VernacCanonical CAst.(make ~loc @@ ByNotation ntn) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Canonical"))),
                                          (Extend.Atoken (Tok.IDENT "Structure"))),
                             (Extend.Aentry global)),
                (fun qid _ _ loc ->
                 VernacCanonical CAst.(make ~loc @@ AN qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Strategy"))),
                             (Extend.Alist1 (Extend.Arules [Extend.Rules 
                                                           ({ Extend.norec_rule = Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Next 
                                                           (Extend.Stop,
                                                           (Extend.Aentry strategy_level)),
                                                           (Extend.Atoken (Tok.KEYWORD "["))),
                                                           (Extend.Alist1 (Extend.Aentry smart_global))),
                                                           (Extend.Atoken (Tok.KEYWORD "]"))) },
                                                           (fun _ q _ v
                                                           loc ->  (v,q) ))]))),
                (fun l _ loc ->  VernacSetStrategy l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Opaque"))),
                             (Extend.Alist1 (Extend.Aentry smart_global))),
                (fun l _ loc ->  VernacSetOpacity (Conv_oracle.Opaque, l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Transparent"))),
                             (Extend.Alist1 (Extend.Aentry smart_global))),
                (fun l _ loc ->
                 VernacSetOpacity (Conv_oracle.transparent, l) ))])])
        in let () =
        Gram.gram_extend arguments_modifier
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "clear"))),
                                                        (Extend.Atoken (Tok.IDENT "implicits"))),
                                           (Extend.Atoken (Tok.IDENT "and"))),
                              (Extend.Atoken (Tok.IDENT "scopes"))),
                 (fun _ _ _ _ loc ->  [`ClearImplicits; `ClearScopes] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "clear"))),
                                                       (Extend.Atoken (Tok.IDENT "scopes"))),
                                          (Extend.Atoken (Tok.IDENT "and"))),
                             (Extend.Atoken (Tok.IDENT "implicits"))),
                (fun _ _ _ _ loc ->  [`ClearImplicits; `ClearScopes] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "extra"))),
                             (Extend.Atoken (Tok.IDENT "scopes"))),
                (fun _ _ loc ->  [`ExtraScopes] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "assert"))),
                (fun _ loc ->  [`Assert] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "rename"))),
                (fun _ loc ->  [`Rename] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "clear"))),
                             (Extend.Atoken (Tok.IDENT "scopes"))),
                (fun _ _ loc ->  [`ClearScopes] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "clear"))),
                             (Extend.Atoken (Tok.IDENT "implicits"))),
                (fun _ _ loc ->  [`ClearImplicits] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "default"))),
                             (Extend.Atoken (Tok.IDENT "implicits"))),
                (fun _ _ loc ->  [`DefaultImplicits] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "simpl"))),
                             (Extend.Atoken (Tok.IDENT "never"))),
                (fun _ _ loc ->  [`ReductionNeverUnfold] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "simpl"))),
                             (Extend.Atoken (Tok.IDENT "nomatch"))),
                (fun _ _ loc ->  [`ReductionDontExposeCase] ))])])
        in let () =
        Gram.gram_extend scope
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "%"))),
                              (Extend.Atoken (Tok.IDENT ""))),
                 (fun key _ loc ->  key ))])])
        in let () =
        Gram.gram_extend argument_spec
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Aopt (Extend.Atoken (Tok.KEYWORD "!")))),
                                           (Extend.Aentry name)),
                              (Extend.Aopt (Extend.Aentry scope))),
                 (fun s id b loc ->
                  id.CAst.v, not (Option.is_empty b), Option.map (fun x -> CAst.make ~loc x) s ))])])
        in let () =
        Gram.gram_extend argument_spec_block
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "{"))),
                                                        (Extend.Alist1 (Extend.Aentry argument_spec))),
                                           (Extend.Atoken (Tok.KEYWORD "}"))),
                              (Extend.Aopt (Extend.Aentry scope))),
                 (fun sc _ items _ loc ->
                  let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc y) x
         | Some _, Some _ -> user_err Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           `Id { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = MaximallyImplicit}) items ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "["))),
                                                       (Extend.Alist1 (Extend.Aentry argument_spec))),
                                          (Extend.Atoken (Tok.KEYWORD "]"))),
                             (Extend.Aopt (Extend.Aentry scope))),
                (fun sc _ items _ loc ->
                 let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc y) x
         | Some _, Some _ -> user_err Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           `Id { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = Implicit}) items ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                       (Extend.Alist1 (Extend.Aentry argument_spec))),
                                          (Extend.Atoken (Tok.KEYWORD ")"))),
                             (Extend.Aopt (Extend.Aentry scope))),
                (fun sc _ items _ loc ->
                 let f x = match sc, x with
         | None, x -> x | x, None -> Option.map (fun y -> CAst.make ~loc y) x
         | Some _, Some _ -> user_err Pp.(str "scope declared twice") in
       List.map (fun (name,recarg_like,notation_scope) ->
           `Id { name=name; recarg_like=recarg_like;
                 notation_scope=f notation_scope;
                 implicit_status = NotImplicit}) items ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "/"))),
                (fun _ loc ->  [`Slash] ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry argument_spec)),
                (fun item loc ->
                 let name, recarg_like, notation_scope = item in
      [`Id { name=name; recarg_like=recarg_like;
             notation_scope=notation_scope;
             implicit_status = NotImplicit}] ))])])
        in let () =
        Gram.gram_extend more_implicits_block
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "{"))),
                                           (Extend.Alist1 (Extend.Aentry name))),
                              (Extend.Atoken (Tok.KEYWORD "}"))),
                 (fun _ items _ loc ->
                  List.map (fun name -> (name.CAst.v, Vernacexpr.MaximallyImplicit)) items ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "["))),
                                          (Extend.Alist1 (Extend.Aentry name))),
                             (Extend.Atoken (Tok.KEYWORD "]"))),
                (fun _ items _ loc ->
                 List.map (fun name -> (name.CAst.v, Vernacexpr.Implicit)) items ));
                Extend.Rule (Extend.Next (Extend.Stop, (Extend.Aentry name)),
                (fun name loc ->  [(name.CAst.v, Vernacexpr.NotImplicit)] ))])])
        in let () =
        Gram.gram_extend strategy_level
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "transparent"))),
                 (fun _ loc ->  Conv_oracle.transparent ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "-"))),
                             (Extend.Atoken (Tok.INT ""))),
                (fun n _ loc ->  Conv_oracle.Level (- int_of_string n) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.INT ""))),
                (fun n loc ->  Conv_oracle.Level (int_of_string n) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "opaque"))),
                (fun _ loc ->  Conv_oracle.Opaque ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "expand"))),
                (fun _ loc ->  Conv_oracle.Expand ))])])
        in let () =
        Gram.gram_extend instance_name
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->  ((CAst.make ~loc Anonymous), None), []  ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry ident_decl)),
                             (Extend.Aopt (Extend.Aentry binders))),
                (fun sup name loc ->
                 (CAst.map (fun id -> Name id) (fst name), snd name),
          (Option.default [] sup) ))])])
        in let () =
        Gram.gram_extend hint_info
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->
                  { Typeclasses.hint_priority = None; hint_pattern = None } ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "|"))),
                                          (Extend.Aopt (Extend.Aentry natural))),
                             (Extend.Aopt (Extend.Aentry constr_pattern))),
                (fun pat i _ loc ->
                 { Typeclasses.hint_priority = i; hint_pattern = pat } ))])])
        in let () =
        Gram.gram_extend reserv_list
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry simple_reserv)),
                 (fun b loc ->  [b] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Alist1 (Extend.Aentry reserv_tuple))),
                (fun bl loc ->  bl ))])])
        in let () =
        Gram.gram_extend reserv_tuple
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "("))),
                                           (Extend.Aentry simple_reserv)),
                              (Extend.Atoken (Tok.KEYWORD ")"))),
                 (fun _ a _ loc ->  a ))])])
        in let () =
        Gram.gram_extend simple_reserv
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Alist1 (Extend.Aentry identref))),
                                           (Extend.Atoken (Tok.KEYWORD ":"))),
                              (Extend.Aentry lconstr)),
                 (fun c _ idl loc ->  (idl,c) ))])])
        in ()

let _ = let printable = Gram.Entry.create "printable"
        and locatable = Gram.Entry.create "locatable"
        and option_value = Gram.Entry.create "option_value"
        and option_ref_value = Gram.Entry.create "option_ref_value"
        and option_table = Gram.Entry.create "option_table"
        and as_dirpath = Gram.Entry.create "as_dirpath"
        and ne_in_or_out_modules = Gram.Entry.create "ne_in_or_out_modules"
        and in_or_out_modules = Gram.Entry.create "in_or_out_modules"
        and comment = Gram.Entry.create "comment"
        and positive_search_mark = Gram.Entry.create "positive_search_mark"
        and scope = Gram.Entry.create "scope"
        and searchabout_query = Gram.Entry.create "searchabout_query"
        and searchabout_queries = Gram.Entry.create "searchabout_queries"
        and univ_name_list = Gram.Entry.create "univ_name_list"
        in
        let () =
        Gram.gram_extend gallina_ext
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Export"))),
                                           (Extend.Atoken (Tok.IDENT "Unset"))),
                              (Extend.Aentry option_table)),
                 (fun table _ _ loc ->  VernacUnsetOption (true, table) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Export"))),
                                                       (Extend.Atoken (Tok.KEYWORD "Set"))),
                                          (Extend.Aentry option_table)),
                             (Extend.Aentry option_value)),
                (fun v table _ _ loc ->  VernacSetOption (true, table, v) ))])])
        in let () =
        Gram.gram_extend command
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Remove"))),
                                           (Extend.Atoken (Tok.IDENT ""))),
                              (Extend.Alist1 (Extend.Aentry option_ref_value))),
                 (fun v table _ loc ->  VernacRemoveOption ([table], v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Remove"))),
                                                       (Extend.Atoken (Tok.IDENT ""))),
                                          (Extend.Atoken (Tok.IDENT ""))),
                             (Extend.Alist1 (Extend.Aentry option_ref_value))),
                (fun v field table _ loc ->
                 VernacRemoveOption ([table;field], v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Test"))),
                             (Extend.Aentry option_table)),
                (fun table _ loc ->  VernacPrintOption table ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Test"))),
                                                       (Extend.Aentry option_table)),
                                          (Extend.Atoken (Tok.KEYWORD "for"))),
                             (Extend.Alist1 (Extend.Aentry option_ref_value))),
                (fun v _ table _ loc ->  VernacMemOption (table, v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Add"))),
                                          (Extend.Atoken (Tok.IDENT ""))),
                             (Extend.Alist1 (Extend.Aentry option_ref_value))),
                (fun v table _ loc ->  VernacAddOption ([table], v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Add"))),
                                                       (Extend.Atoken (Tok.IDENT ""))),
                                          (Extend.Atoken (Tok.IDENT ""))),
                             (Extend.Alist1 (Extend.Aentry option_ref_value))),
                (fun v field table _ loc ->
                 VernacAddOption ([table;field], v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Print"))),
                                          (Extend.Atoken (Tok.IDENT "Table"))),
                             (Extend.Aentry option_table)),
                (fun table _ _ loc ->  VernacPrintOption table ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Unset"))),
                             (Extend.Aentry option_table)),
                (fun table _ loc ->  VernacUnsetOption (false, table) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "Set"))),
                                          (Extend.Aentry option_table)),
                             (Extend.Aentry option_value)),
                (fun v table _ loc ->  VernacSetOption (false, table, v) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Add"))),
                                                                    (Extend.Atoken (Tok.IDENT "Rec"))),
                                                       (Extend.Atoken (Tok.IDENT "ML"))),
                                          (Extend.Atoken (Tok.IDENT "Path"))),
                             (Extend.Aentry ne_string)),
                (fun dir _ _ _ _ loc ->  VernacAddMLPath (true, dir) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Add"))),
                                                       (Extend.Atoken (Tok.IDENT "ML"))),
                                          (Extend.Atoken (Tok.IDENT "Path"))),
                             (Extend.Aentry ne_string)),
                (fun dir _ _ _ loc ->  VernacAddMLPath (false, dir) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Inspect"))),
                             (Extend.Aentry natural)),
                (fun n _ loc ->  VernacPrint (PrintInspect n) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Print"))),
                                          (Extend.Atoken (Tok.IDENT "Namespace"))),
                             (Extend.Aentry dirpath)),
                (fun ns _ _ loc ->  VernacPrint (PrintNamespace ns) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Print"))),
                                          (Extend.Atoken (Tok.IDENT "Module"))),
                             (Extend.Aentry global)),
                (fun qid _ _ loc ->  VernacPrint (PrintModule qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Print"))),
                                                       (Extend.Atoken (Tok.IDENT "Module"))),
                                          (Extend.Atoken (Tok.KEYWORD "Type"))),
                             (Extend.Aentry global)),
                (fun qid _ _ _ loc ->  VernacPrint (PrintModuleType qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Print"))),
                                          (Extend.Aentry smart_global)),
                             (Extend.Aopt (Extend.Aentry univ_name_list))),
                (fun l qid _ loc ->  VernacPrint (PrintName (qid,l)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Print"))),
                             (Extend.Aentry printable)),
                (fun p _ loc ->  VernacPrint p ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "Type"))),
                             (Extend.Aentry lconstr)),
                (fun c _ loc ->  VernacGlobalCheck c ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "DelPath"))),
                             (Extend.Aentry ne_string)),
                (fun dir _ loc ->  VernacRemoveLoadPath dir ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "AddRecPath"))),
                                                       (Extend.Aentry ne_string)),
                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                             (Extend.Aentry as_dirpath)),
                (fun alias _ dir _ loc ->
                 VernacAddLoadPath (true, dir, alias) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "AddPath"))),
                                                       (Extend.Aentry ne_string)),
                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                             (Extend.Aentry as_dirpath)),
                (fun alias _ dir _ loc ->
                 VernacAddLoadPath (false, dir, alias) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Remove"))),
                                          (Extend.Atoken (Tok.IDENT "LoadPath"))),
                             (Extend.Aentry ne_string)),
                (fun dir _ _ loc ->  VernacRemoveLoadPath dir ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Add"))),
                                                                    (Extend.Atoken (Tok.IDENT "Rec"))),
                                                       (Extend.Atoken (Tok.IDENT "LoadPath"))),
                                          (Extend.Aentry ne_string)),
                             (Extend.Aentry as_dirpath)),
                (fun alias dir _ _ _ loc ->
                 VernacAddLoadPath (true, dir, alias) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Add"))),
                                                       (Extend.Atoken (Tok.IDENT "LoadPath"))),
                                          (Extend.Aentry ne_string)),
                             (Extend.Aentry as_dirpath)),
                (fun alias dir _ _ loc ->
                 VernacAddLoadPath (false, dir, alias) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Locate"))),
                             (Extend.Aentry locatable)),
                (fun l _ loc ->  VernacLocate l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Declare"))),
                                                       (Extend.Atoken (Tok.IDENT "ML"))),
                                          (Extend.Atoken (Tok.IDENT "Module"))),
                             (Extend.Alist1 (Extend.Aentry ne_string))),
                (fun l _ _ _ loc ->  VernacDeclareMLModule l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Load"))),
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Stop },
                                                         (fun loc ->
                                                          false ));
                                                         Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.IDENT "Verbose"))) },
                                                         (fun _ loc ->
                                                          true ))])),
                             (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.IDENT ""))) },
                                                          (fun s loc -> 
                                                           s ));
                                            Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Aentry ne_string)) },
                                                         (fun s loc -> 
                                                          s ))])),
                (fun s verbosely _ loc ->  VernacLoad (verbosely, s) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Cd"))),
                             (Extend.Aentry ne_string)),
                (fun dir _ loc ->  VernacChdir (Some dir) ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "Cd"))),
                (fun _ loc ->  VernacChdir None ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "Pwd"))),
                (fun _ loc ->  VernacChdir None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Declare"))),
                                                                    (Extend.Atoken (Tok.IDENT "Instance"))),
                                                                    (Extend.Aentry instance_name)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":"))),
                                                       (Extend.Arules 
                                                       [Extend.Rules 
                                                       ({ Extend.norec_rule = Extend.Stop },
                                                       (fun loc ->
                                                        Decl_kinds.Explicit ));
                                                       Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "!"))) },
                                                                    (fun _
                                                                    loc ->
                                                                     Decl_kinds.Implicit ))])),
                                          (Extend.Aentryl (operconstr, "200"))),
                             (Extend.Aentry hint_info)),
                (fun info t expl _ namesup _ _ loc ->
                 VernacInstance (true, snd namesup, (fst namesup, expl, t), None, info) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Comments"))),
                             (Extend.Alist0 (Extend.Aentry comment))),
                (fun l _ loc ->  VernacComments l ))])])
        in let () =
        Gram.gram_extend query_command
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "SearchAbout"))),
                                                        (Extend.Atoken (Tok.KEYWORD "["))),
                                                        (Extend.Alist1 (Extend.Aentry searchabout_query))),
                                                        (Extend.Atoken (Tok.KEYWORD "]"))),
                                           (Extend.Aentry in_or_out_modules)),
                              (Extend.Atoken (Tok.KEYWORD "."))),
                 (fun _ l _ sl _ _ loc ->
                  fun g -> VernacSearch (SearchAbout sl,g, l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "SearchAbout"))),
                                                       (Extend.Aentry searchabout_query)),
                                          (Extend.Aentry searchabout_queries)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ l s _ loc ->
                 fun g -> let (sl,m) = l in VernacSearch (SearchAbout (s::sl),g, m) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Search"))),
                                                       (Extend.Aentry searchabout_query)),
                                          (Extend.Aentry searchabout_queries)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ l s _ loc ->
                 let (sl,m) = l in fun g -> VernacSearch (SearchAbout (s::sl),g, m) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "SearchRewrite"))),
                                                       (Extend.Aentry constr_pattern)),
                                          (Extend.Aentry in_or_out_modules)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ l c _ loc ->
                 fun g -> VernacSearch (SearchRewrite c,g, l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "SearchPattern"))),
                                                       (Extend.Aentry constr_pattern)),
                                          (Extend.Aentry in_or_out_modules)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ l c _ loc ->
                 fun g -> VernacSearch (SearchPattern c,g, l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "SearchHead"))),
                                                       (Extend.Aentry constr_pattern)),
                                          (Extend.Aentry in_or_out_modules)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ l c _ loc ->
                 fun g -> VernacSearch (SearchHead c,g, l) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "About"))),
                                                       (Extend.Aentry smart_global)),
                                          (Extend.Aopt (Extend.Aentry univ_name_list))),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ l qid _ loc ->
                 fun g -> VernacPrint (PrintAbout (qid,l,g)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Check"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ c _ loc ->  fun g -> VernacCheckMayEval (None, g, c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Compute"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ c _ loc ->
                 fun g -> VernacCheckMayEval (Some (Genredexpr.CbvVm None), g, c) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Eval"))),
                                                                    (Extend.Aentry red_expr)),
                                                       (Extend.Atoken (Tok.KEYWORD "in"))),
                                          (Extend.Aentry lconstr)),
                             (Extend.Atoken (Tok.KEYWORD "."))),
                (fun _ c _ r _ loc ->
                 fun g -> VernacCheckMayEval (Some r, g, c) ))])])
        in let () =
        Gram.gram_extend printable
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Atoken (Tok.IDENT "Strategies"))),
                 (fun _ loc ->  PrintStrategy None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Strategy"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ loc ->  PrintStrategy (Some qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "All"))),
                                          (Extend.Atoken (Tok.IDENT "Dependencies"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ _ loc ->  PrintAssumptions (true, true, qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Transparent"))),
                                          (Extend.Atoken (Tok.IDENT "Dependencies"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ _ loc ->  PrintAssumptions (false, true, qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Opaque"))),
                                          (Extend.Atoken (Tok.IDENT "Dependencies"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ _ loc ->  PrintAssumptions (true, false, qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Assumptions"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ loc ->  PrintAssumptions (false, false, qid) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Sorted"))),
                                          (Extend.Atoken (Tok.IDENT "Universes"))),
                             (Extend.Aopt (Extend.Aentry ne_string))),
                (fun fopt _ _ loc ->  PrintUniverses (true, fopt) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Universes"))),
                             (Extend.Aopt (Extend.Aentry ne_string))),
                (fun fopt _ loc ->  PrintUniverses (false, fopt) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Implicit"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ loc ->  PrintImplicit qid ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Visibility"))),
                             (Extend.Aopt (Extend.Atoken (Tok.IDENT "")))),
                (fun s _ loc ->  PrintVisibility s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Scope"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun s _ loc ->  PrintScope s ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Scopes"))),
                (fun _ loc ->  PrintScopes ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "HintDb"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun s _ loc ->  PrintHintDbName s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Hint"))),
                             (Extend.Atoken (Tok.KEYWORD "*"))),
                (fun _ _ loc ->  PrintHintDb ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Hint"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ loc ->  PrintHint qid ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Hint"))),
                (fun _ loc ->  PrintHintGoal ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Options"))),
                (fun _ loc ->  PrintTables (* A Synonymous to Tables *) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Tables"))),
                (fun _ loc ->  PrintTables ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Canonical"))),
                             (Extend.Atoken (Tok.IDENT "Projections"))),
                (fun _ _ loc ->  PrintCanonicalConversions ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Coercion"))),
                                                       (Extend.Atoken (Tok.IDENT "Paths"))),
                                          (Extend.Aentry class_rawexpr)),
                             (Extend.Aentry class_rawexpr)),
                (fun t s _ _ loc ->  PrintCoercionPaths (s,t) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Coercions"))),
                (fun _ loc ->  PrintCoercions ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Instances"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ loc ->  PrintInstances qid ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "TypeClasses"))),
                (fun _ loc ->  PrintTypeClasses ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Classes"))),
                (fun _ loc ->   PrintClasses ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Graph"))),
                (fun _ loc ->  PrintGraph ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Debug"))),
                             (Extend.Atoken (Tok.IDENT "GC"))),
                (fun _ _ loc ->  PrintDebugGC ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "ML"))),
                             (Extend.Atoken (Tok.IDENT "Modules"))),
                (fun _ _ loc ->  PrintMLModules ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "ML"))),
                             (Extend.Atoken (Tok.IDENT "Path"))),
                (fun _ _ loc ->  PrintMLLoadPath ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Libraries"))),
                (fun _ loc ->  PrintModules ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Modules"))),
                (fun _ loc ->
                 user_err Pp.(str "Print Modules is obsolete; use Print Libraries instead") ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "LoadPath"))),
                             (Extend.Aopt (Extend.Aentry dirpath))),
                (fun dir _ loc ->  PrintLoadPath dir ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Grammar"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun ent _ loc ->  PrintGrammar ent ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Section"))),
                             (Extend.Aentry global)),
                (fun s _ loc ->  PrintSectionContext s ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "All"))),
                (fun _ loc ->  PrintFullContext ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Term"))),
                                          (Extend.Aentry smart_global)),
                             (Extend.Aopt (Extend.Aentry univ_name_list))),
                (fun l qid _ loc ->  PrintName (qid,l) ))])])
        in let () =
        Gram.gram_extend class_rawexpr
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry smart_global)),
                 (fun qid loc ->  RefClass qid ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Sortclass"))),
                (fun _ loc ->  SortClass ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Funclass"))),
                (fun _ loc ->  FunClass ))])])
        in let () =
        Gram.gram_extend locatable
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT "Module"))),
                              (Extend.Aentry global)),
                 (fun qid _ loc ->  LocateModule qid ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Library"))),
                             (Extend.Aentry global)),
                (fun qid _ loc ->  LocateLibrary qid ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "File"))),
                             (Extend.Aentry ne_string)),
                (fun f _ loc ->  LocateFile f ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Term"))),
                             (Extend.Aentry smart_global)),
                (fun qid _ loc ->  LocateTerm qid ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry smart_global)),
                (fun qid loc ->  LocateAny qid ))])])
        in let () =
        Gram.gram_extend option_value
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.STRING ""))),
                 (fun s loc ->  StringValue s ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry integer)),
                (fun n loc ->  IntValue (Some n) ));
                Extend.Rule (Extend.Stop, (fun loc ->  BoolValue true ))])])
        in let () =
        Gram.gram_extend option_ref_value
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.STRING ""))),
                 (fun s loc ->  StringRefValue s ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry global)),
                (fun id loc ->  QualidRefValue id ))])])
        in let () =
        Gram.gram_extend option_table
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Alist1 (Extend.Arules [Extend.Rules 
                                                            ({ Extend.norec_rule = Extend.Next 
                                                            (Extend.Stop,
                                                            (Extend.Atoken (Tok.IDENT ""))) },
                                                            (fun x loc ->
                                                             x ))]))),
                 (fun fl loc ->  fl ))])])
        in let () =
        Gram.gram_extend as_dirpath
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop,
                              (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                                                          (Extend.Aentry dirpath)) },
                                                          (fun d _ loc ->
                                                           d ))]))),
                 (fun d loc ->  d ))])])
        in let () =
        Gram.gram_extend ne_in_or_out_modules
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT "outside"))),
                              (Extend.Alist1 (Extend.Aentry global))),
                 (fun l _ loc ->  SearchOutside l ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "inside"))),
                             (Extend.Alist1 (Extend.Aentry global))),
                (fun l _ loc ->  SearchInside l ))])])
        in let () =
        Gram.gram_extend in_or_out_modules
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  SearchOutside [] ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentry ne_in_or_out_modules)),
                (fun m loc ->  m ))])])
        in let () =
        Gram.gram_extend comment
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry natural)),
                 (fun n loc ->  CommentInt n ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.STRING ""))),
                (fun s loc ->  CommentString s ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry constr)),
                (fun c loc ->  CommentConstr c ))])])
        in let () =
        Gram.gram_extend positive_search_mark
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  true ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.KEYWORD "-"))),
                (fun _ loc ->  false ))])])
        in let () =
        Gram.gram_extend scope
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "%"))),
                              (Extend.Atoken (Tok.IDENT ""))),
                 (fun key _ loc ->  key ))])])
        in let () =
        Gram.gram_extend searchabout_query
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry positive_search_mark)),
                              (Extend.Aentry constr_pattern)),
                 (fun p b loc ->  (b, SearchSubPattern p) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Aentry positive_search_mark)),
                                          (Extend.Aentry ne_string)),
                             (Extend.Aopt (Extend.Aentry scope))),
                (fun sc s b loc ->  (b, SearchString (s,sc)) ))])])
        in let () =
        Gram.gram_extend searchabout_queries
        (None, [(None, None,
                [Extend.Rule (Extend.Stop,
                 (fun loc ->  ([],SearchOutside []) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry searchabout_query)),
                             (Extend.Aentry searchabout_queries)),
                (fun l s loc ->  let (sl,m) = l in (s::sl,m) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Aentry ne_in_or_out_modules)),
                (fun m loc ->  ([],m) ))])])
        in let () =
        Gram.gram_extend univ_name_list
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "@{"))),
                                           (Extend.Alist0 (Extend.Aentry name))),
                              (Extend.Atoken (Tok.KEYWORD "}"))),
                 (fun _ l _ loc ->  l ))])])
        in ()

let _ = let () =
        Gram.gram_extend command
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Declare"))),
                                                        (Extend.Atoken (Tok.IDENT "Custom"))),
                                           (Extend.Atoken (Tok.IDENT "Entry"))),
                              (Extend.Atoken (Tok.IDENT ""))),
                 (fun s _ _ _ loc ->  VernacDeclareCustomEntry s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Declare"))),
                                                                    (Extend.Atoken (Tok.IDENT "Reduction"))),
                                                       (Extend.Atoken (Tok.IDENT ""))),
                                          (Extend.Atoken (Tok.KEYWORD ":="))),
                             (Extend.Aentry red_expr)),
                (fun r _ s _ _ loc ->  VernacDeclareReduction (s,r) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Debug"))),
                             (Extend.Atoken (Tok.IDENT "Off"))),
                (fun _ _ loc ->
                 VernacSetOption (false, ["Ltac";"Debug"], BoolValue false) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Debug"))),
                             (Extend.Atoken (Tok.IDENT "On"))),
                (fun _ _ loc ->
                 VernacSetOption (false, ["Ltac";"Debug"], BoolValue true) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "BackTo"))),
                             (Extend.Aentry natural)),
                (fun n _ loc ->  VernacBackTo n ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Back"))),
                             (Extend.Aentry natural)),
                (fun n _ loc ->  VernacBack n ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "Back"))),
                (fun _ loc ->  VernacBack 1 ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Reset"))),
                             (Extend.Aentry identref)),
                (fun id _ loc ->  VernacResetName id ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "Reset"))),
                             (Extend.Atoken (Tok.IDENT "Initial"))),
                (fun _ _ loc ->  VernacResetInitial ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Restore"))),
                                          (Extend.Atoken (Tok.IDENT "State"))),
                             (Extend.Aentry ne_string)),
                (fun s _ _ loc ->  VernacRestoreState s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Restore"))),
                                          (Extend.Atoken (Tok.IDENT "State"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun s _ _ loc ->  VernacRestoreState s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Write"))),
                                          (Extend.Atoken (Tok.IDENT "State"))),
                             (Extend.Aentry ne_string)),
                (fun s _ _ loc ->  VernacWriteState s ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Write"))),
                                          (Extend.Atoken (Tok.IDENT "State"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun s _ _ loc ->  VernacWriteState s ))])])
        in ()

let _ = let only_parsing = Gram.Entry.create "only_parsing"
        and level = Gram.Entry.create "level"
        and syntax_modifier = Gram.Entry.create "syntax_modifier"
        and syntax_extension_type = Gram.Entry.create "syntax_extension_type"
        and at_level = Gram.Entry.create "at_level"
        and constr_as_binder_kind = Gram.Entry.create "constr_as_binder_kind"
        in
        let () =
        Gram.gram_extend syntax
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "Reserved"))),
                                                        (Extend.Atoken (Tok.IDENT "Notation"))),
                                           (Extend.Aentry ne_lstring)),
                              (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Stop },
                                                           (fun loc -> 
                                                            [] ));
                                             Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "("))),
                                                          (Extend.Alist1sep ((Extend.Aentry syntax_modifier), (Extend.Atoken (Tok.KEYWORD ","))))),
                                                          (Extend.Atoken (Tok.KEYWORD ")"))) },
                                                          (fun _ l _ loc ->
                                                           l ))])),
                 (fun l s _ _ loc ->  VernacSyntaxExtension (false, (s,l)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Reserved"))),
                                                       (Extend.Atoken (Tok.IDENT "Infix"))),
                                          (Extend.Aentry ne_lstring)),
                             (Extend.Arules [Extend.Rules ({ Extend.norec_rule = Extend.Stop },
                                                          (fun loc -> 
                                                           [] ));
                                            Extend.Rules ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "("))),
                                                         (Extend.Alist1sep ((Extend.Aentry syntax_modifier), (Extend.Atoken (Tok.KEYWORD ","))))),
                                                         (Extend.Atoken (Tok.KEYWORD ")"))) },
                                                         (fun _ l _ loc ->
                                                          l ))])),
                (fun l s _ _ loc ->
                 let s = CAst.map (fun s -> "x '"^s^"' y") s in
           VernacSyntaxExtension (true,(s,l)) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Format"))),
                                                                    (Extend.Atoken (Tok.IDENT "Notation"))),
                                                       (Extend.Atoken (Tok.STRING ""))),
                                          (Extend.Atoken (Tok.STRING ""))),
                             (Extend.Atoken (Tok.STRING ""))),
                (fun fmt s n _ _ loc ->  VernacNotationAddFormat (n,s,fmt) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Notation"))),
                                                                    (Extend.Aentry lstring)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":="))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Stop },
                                                         (fun loc -> 
                                                          [] ));
                                                         Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "("))),
                                                         (Extend.Alist1sep ((Extend.Aentry syntax_modifier), (Extend.Atoken (Tok.KEYWORD ","))))),
                                                         (Extend.Atoken (Tok.KEYWORD ")"))) },
                                                         (fun _ l _ loc ->
                                                          l ))])),
                             (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD ":"))),
                                                         (Extend.Atoken (Tok.IDENT ""))) },
                                                         (fun sc _ loc ->
                                                          sc ))]))),
                (fun sc modl c _ s _ loc ->  VernacNotation (c,(s,modl),sc) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Notation"))),
                                                                    (Extend.Aentry identref)),
                                                                    (Extend.Alist0 (Extend.Aentry ident))),
                                                       (Extend.Atoken (Tok.KEYWORD ":="))),
                                          (Extend.Aentry constr)),
                             (Extend.Aentry only_parsing)),
                (fun b c _ idl id _ loc ->
                 VernacSyntacticDefinition
             (id,(idl,c),b) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Infix"))),
                                                                    (Extend.Aentry ne_lstring)),
                                                                    (Extend.Atoken (Tok.KEYWORD ":="))),
                                                       (Extend.Aentry constr)),
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Stop },
                                                         (fun loc -> 
                                                          [] ));
                                                         Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD "("))),
                                                         (Extend.Alist1sep ((Extend.Aentry syntax_modifier), (Extend.Atoken (Tok.KEYWORD ","))))),
                                                         (Extend.Atoken (Tok.KEYWORD ")"))) },
                                                         (fun _ l _ loc ->
                                                          l ))])),
                             (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.KEYWORD ":"))),
                                                         (Extend.Atoken (Tok.IDENT ""))) },
                                                         (fun sc _ loc ->
                                                          sc ))]))),
                (fun sc modl p _ op _ loc ->  VernacInfix ((op,modl),p,sc) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Bind"))),
                                                                    (Extend.Atoken (Tok.IDENT "Scope"))),
                                                       (Extend.Atoken (Tok.IDENT ""))),
                                          (Extend.Atoken (Tok.KEYWORD "with"))),
                             (Extend.Alist1 (Extend.Aentry class_rawexpr))),
                (fun refl _ sc _ _ loc ->  VernacBindScope (sc,refl) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Undelimit"))),
                                          (Extend.Atoken (Tok.IDENT "Scope"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun sc _ _ loc ->  VernacDelimiters (sc, None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "Delimit"))),
                                                                    (Extend.Atoken (Tok.IDENT "Scope"))),
                                                       (Extend.Atoken (Tok.IDENT ""))),
                                          (Extend.Atoken (Tok.KEYWORD "with"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun key _ sc _ _ loc ->  VernacDelimiters (sc, Some key) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Close"))),
                                          (Extend.Atoken (Tok.IDENT "Scope"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun sc _ _ loc ->  VernacOpenCloseScope (false,sc) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "Open"))),
                                          (Extend.Atoken (Tok.IDENT "Scope"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun sc _ _ loc ->  VernacOpenCloseScope (true,sc) ))])])
        in let () =
        Gram.gram_extend only_parsing
        (None, [(None, None,
                [Extend.Rule (Extend.Stop, (fun loc ->  None ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                       (Extend.Atoken (Tok.IDENT "compat"))),
                                          (Extend.Atoken (Tok.STRING ""))),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ s _ _ loc ->  Some (parse_compat_version s) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "("))),
                                                       (Extend.Atoken (Tok.IDENT "only"))),
                                          (Extend.Atoken (Tok.IDENT "parsing"))),
                             (Extend.Atoken (Tok.KEYWORD ")"))),
                (fun _ _ _ _ loc ->  Some Flags.Current ))])])
        in let () =
        Gram.gram_extend level
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT "next"))),
                              (Extend.Atoken (Tok.IDENT "level"))),
                 (fun _ _ loc ->  NextLevel ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "level"))),
                             (Extend.Aentry natural)),
                (fun n _ loc ->  NumLevel n ))])])
        in let () =
        Gram.gram_extend syntax_modifier
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.IDENT ""))),
                              (Extend.Aentry syntax_extension_type)),
                 (fun typ x loc ->  SetEntryType (x,typ) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT ""))),
                             (Extend.Aentry constr_as_binder_kind)),
                (fun b x loc ->  SetItemLevel ([x],Some b,None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT ""))),
                                                       (Extend.Atoken (Tok.KEYWORD "at"))),
                                          (Extend.Aentry level)),
                             (Extend.Aentry constr_as_binder_kind)),
                (fun b lev _ x loc ->  SetItemLevel ([x],Some b,Some lev) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT ""))),
                                          (Extend.Atoken (Tok.KEYWORD "at"))),
                             (Extend.Aentry level)),
                (fun lev _ x loc ->  SetItemLevel ([x],None,Some lev) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT ""))),
                                                                    (Extend.Atoken (Tok.KEYWORD ","))),
                                                       (Extend.Alist1sep ((Extend.Arules 
                                                       [Extend.Rules 
                                                       ({ Extend.norec_rule = Extend.Next 
                                                       (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT ""))) },
                                                       (fun id loc -> 
                                                        id ))]), (Extend.Atoken (Tok.KEYWORD ","))))),
                                          (Extend.Atoken (Tok.KEYWORD "at"))),
                             (Extend.Aentry level)),
                (fun lev _ l _ x loc ->  SetItemLevel (x::l,None,Some lev) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "format"))),
                                          (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.STRING ""))) },
                                                         (fun s loc ->
                                                          CAst.make ~loc s ))])),
                             (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                         ({ Extend.norec_rule = Extend.Next 
                                                         (Extend.Stop,
                                                         (Extend.Atoken (Tok.STRING ""))) },
                                                         (fun s loc ->
                                                          CAst.make ~loc s ))]))),
                (fun s2 s1 _ loc ->
                 begin match s1, s2 with
          | { CAst.v = k }, Some s -> SetFormat(k,s)
          | s, None -> SetFormat ("text",s) end ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "compat"))),
                             (Extend.Atoken (Tok.STRING ""))),
                (fun s _ loc ->  SetCompatVersion (parse_compat_version s) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "only"))),
                             (Extend.Atoken (Tok.IDENT "parsing"))),
                (fun _ _ loc ->  SetOnlyParsing ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "only"))),
                             (Extend.Atoken (Tok.IDENT "printing"))),
                (fun _ _ loc ->  SetOnlyPrinting ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "no"))),
                             (Extend.Atoken (Tok.IDENT "associativity"))),
                (fun _ _ loc ->  SetAssoc NonA ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "right"))),
                             (Extend.Atoken (Tok.IDENT "associativity"))),
                (fun _ _ loc ->  SetAssoc RightA ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "left"))),
                             (Extend.Atoken (Tok.IDENT "associativity"))),
                (fun _ _ loc ->  SetAssoc LeftA ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.KEYWORD "in"))),
                                                                    (Extend.Atoken (Tok.IDENT "custom"))),
                                                                    (Extend.Atoken (Tok.IDENT ""))),
                                                       (Extend.Atoken (Tok.KEYWORD "at"))),
                                          (Extend.Atoken (Tok.IDENT "level"))),
                             (Extend.Aentry natural)),
                (fun n _ _ x _ _ loc ->  SetCustomEntry (x,Some n) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "in"))),
                                          (Extend.Atoken (Tok.IDENT "custom"))),
                             (Extend.Atoken (Tok.IDENT ""))),
                (fun x _ _ loc ->  SetCustomEntry (x,None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.KEYWORD "at"))),
                                          (Extend.Atoken (Tok.IDENT "level"))),
                             (Extend.Aentry natural)),
                (fun n _ _ loc ->  SetLevel n ))])])
        in let () =
        Gram.gram_extend syntax_extension_type
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                        (Extend.Stop,
                                                        (Extend.Atoken (Tok.IDENT "custom"))),
                                                        (Extend.Atoken (Tok.IDENT ""))),
                                           (Extend.Aopt (Extend.Aentry at_level))),
                              (Extend.Aopt (Extend.Aentry constr_as_binder_kind))),
                 (fun b n x _ loc ->  ETConstr (InCustomEntry x,b,n) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "closed"))),
                             (Extend.Atoken (Tok.IDENT "binder"))),
                (fun _ _ loc ->  ETBinder false ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Next 
                                                                    (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "strict"))),
                                                                    (Extend.Atoken (Tok.IDENT "pattern"))),
                                                       (Extend.Atoken (Tok.KEYWORD "at"))),
                                          (Extend.Atoken (Tok.IDENT "level"))),
                             (Extend.Aentry natural)),
                (fun n _ _ _ _ loc ->  ETPattern (true,Some n) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.IDENT "strict"))),
                             (Extend.Atoken (Tok.IDENT "pattern"))),
                (fun _ _ loc ->  ETPattern (true,None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                                    (Extend.Atoken (Tok.IDENT "pattern"))),
                                                       (Extend.Atoken (Tok.KEYWORD "at"))),
                                          (Extend.Atoken (Tok.IDENT "level"))),
                             (Extend.Aentry natural)),
                (fun n _ _ _ loc ->  ETPattern (false,Some n) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "pattern"))),
                (fun _ loc ->  ETPattern (false,None) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                       (Extend.Atoken (Tok.IDENT "constr"))),
                                          (Extend.Aopt (Extend.Aentry at_level))),
                             (Extend.Aopt (Extend.Aentry constr_as_binder_kind))),
                (fun b n _ loc ->  ETConstr (InConstrEntry,b,n) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "constr"))),
                (fun _ loc ->  ETConstr (InConstrEntry,None,None) ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "binder"))),
                (fun _ loc ->  ETBinder true ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "bigint"))),
                (fun _ loc ->  ETBigint ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "global"))),
                (fun _ loc ->  ETGlobal ));
                Extend.Rule
                (Extend.Next (Extend.Stop,
                             (Extend.Atoken (Tok.IDENT "ident"))),
                (fun _ loc ->  ETIdent ))])])
        in let () =
        Gram.gram_extend at_level
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "at"))),
                              (Extend.Aentry level)),
                 (fun n _ loc ->  n ))])])
        in let () =
        Gram.gram_extend constr_as_binder_kind
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Next (Extend.Stop,
                                                        (Extend.Atoken (Tok.KEYWORD "as"))),
                                           (Extend.Atoken (Tok.IDENT "strict"))),
                              (Extend.Atoken (Tok.IDENT "pattern"))),
                 (fun _ _ _ loc ->  Notation_term.AsStrictPattern ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                             (Extend.Atoken (Tok.IDENT "pattern"))),
                (fun _ _ loc ->  Notation_term.AsIdentOrPattern ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Atoken (Tok.KEYWORD "as"))),
                             (Extend.Atoken (Tok.IDENT "ident"))),
                (fun _ _ loc ->  Notation_term.AsIdent ))])])
        in ()




open Names
open Libnames

open Pcoq
open Pcoq.Prim

let prim_kw = ["{"; "}"; "["; "]"; "("; ")"; "'"]
let _ = List.iter CLexer.add_keyword prim_kw


let local_make_qualid loc l id = make_qualid ~loc (DirPath.make l) id

let my_int_of_string loc s =
  try
    int_of_string s
  with Failure _ ->
    CErrors.user_err ~loc (Pp.str "This number is too large.")


let _ = let field = Gram.Entry.create "field"
        and fields = Gram.Entry.create "fields"
        and basequalid = Gram.Entry.create "basequalid"
        in
        let () =
        Gram.gram_extend preident
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT ""))),
                 (fun s loc ->  s ))])])
        in let () =
        Gram.gram_extend ident
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT ""))),
                 (fun s loc ->  Id.of_string s ))])])
        in let () =
        Gram.gram_extend pattern_ident
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.LEFTQMARK))),
                              (Extend.Aentry ident)),
                 (fun id _ loc ->  id ))])])
        in let () =
        Gram.gram_extend pattern_identref
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry pattern_ident)),
                 (fun id loc ->  CAst.make ~loc id ))])])
        in let () =
        Gram.gram_extend var
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                 (fun id loc ->  CAst.make ~loc id ))])])
        in let () =
        Gram.gram_extend identref
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                 (fun id loc ->  CAst.make ~loc id ))])])
        in let () =
        Gram.gram_extend field
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.FIELD ""))),
                 (fun s loc ->  Id.of_string s ))])])
        in let () =
        Gram.gram_extend fields
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry field)),
                 (fun id loc ->  ([],id) ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry field)),
                             (Extend.Aentry fields)),
                (fun f id loc ->  let (l,id') = f in (l@[id],id') ))])])
        in let () =
        Gram.gram_extend fullyqualid
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                 (fun id loc ->  CAst.make ~loc [id] ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry ident)),
                             (Extend.Aentry fields)),
                (fun f id loc ->
                 let (l,id') = f in CAst.make ~loc @@ id::List.rev (id'::l) ))])])
        in let () =
        Gram.gram_extend basequalid
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                 (fun id loc ->  qualid_of_ident ~loc id ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry ident)),
                             (Extend.Aentry fields)),
                (fun f id loc ->
                 let (l,id') = f in  local_make_qualid loc (l@[id]) id' ))])])
        in let () =
        Gram.gram_extend name
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                 (fun id loc ->  CAst.make ~loc @@ Name id ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.IDENT "_"))),
                (fun _ loc ->  CAst.make ~loc Anonymous ))])])
        in let () =
        Gram.gram_extend reference
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ident)),
                 (fun id loc ->  local_make_qualid loc [] id ));
                Extend.Rule
                (Extend.Next (Extend.Next (Extend.Stop,
                                          (Extend.Aentry ident)),
                             (Extend.Aentry fields)),
                (fun f id loc ->
                
        let (l,id') = f in
        local_make_qualid loc (l@[id]) id' ))])])
        in let () =
        Gram.gram_extend by_notation
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry ne_string)),
                              (Extend.Aopt (Extend.Arules [Extend.Rules 
                                                          ({ Extend.norec_rule = Extend.Next 
                                                          (Extend.Next 
                                                          (Extend.Stop,
                                                          (Extend.Atoken (Tok.KEYWORD "%"))),
                                                          (Extend.Atoken (Tok.IDENT ""))) },
                                                          (fun key _ loc ->
                                                           key ))]))),
                 (fun sc s loc ->  (s, sc) ))])])
        in let () =
        Gram.gram_extend smart_global
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry by_notation)),
                 (fun ntn loc ->
                  CAst.make ~loc @@ Constrexpr.ByNotation ntn ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Aentry reference)),
                (fun c loc ->  CAst.make ~loc @@ Constrexpr.AN c ))])])
        in let () =
        Gram.gram_extend qualid
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry basequalid)),
                 (fun qid loc ->  qid ))])])
        in let () =
        Gram.gram_extend ne_string
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.STRING ""))),
                 (fun s loc ->
                  if s="" then CErrors.user_err ~loc (Pp.str"Empty string."); s ))])])
        in let () =
        Gram.gram_extend ne_lstring
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry ne_string)),
                 (fun s loc ->  CAst.make ~loc s ))])])
        in let () =
        Gram.gram_extend dirpath
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Aentry ident)),
                              (Extend.Alist0 (Extend.Aentry field))),
                 (fun l id loc ->  DirPath.make (List.rev (id::l)) ))])])
        in let () =
        Gram.gram_extend string
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.STRING ""))),
                 (fun s loc ->  s ))])])
        in let () =
        Gram.gram_extend lstring
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Aentry string)),
                 (fun s loc ->  CAst.make ~loc s ))])])
        in let () =
        Gram.gram_extend integer
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Next (Extend.Stop,
                                           (Extend.Atoken (Tok.KEYWORD "-"))),
                              (Extend.Atoken (Tok.INT ""))),
                 (fun i _ loc ->  - my_int_of_string loc i ));
                Extend.Rule
                (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.INT ""))),
                (fun i loc ->  my_int_of_string loc i ))])])
        in let () =
        Gram.gram_extend natural
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.INT ""))),
                 (fun i loc ->  my_int_of_string loc i ))])])
        in let () =
        Gram.gram_extend bigint
        (None, [(None, None,
                [Extend.Rule
                 (Extend.Next (Extend.Stop, (Extend.Atoken (Tok.INT ""))),
                 (fun i loc ->  i ))])])
        in ()


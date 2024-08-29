open AClightLib

let rec var_to_temp = function
  | Clight.Evar (id, typ) -> Clight.Etempvar (id, typ)
  | Clight.Ederef (e, typ) -> Clight.Ederef (var_to_temp e, typ)
  | Clight.Eaddrof (e, typ) -> Clight.Eaddrof (var_to_temp e, typ)
  | Clight.Eunop (uop, e, typ) -> Clight.Eunop (uop, var_to_temp e, typ)
  | Clight.Ebinop (bop, e1, e2, typ) ->
      Clight.Ebinop (bop, var_to_temp e1, var_to_temp e2, typ)
  | Clight.Ecast (e, typ) -> Clight.Ecast (var_to_temp e, typ)
  | Clight.Efield (e, fid, typ) -> Clight.Efield (var_to_temp e, fid, typ)
  | e -> e

let convertPClight csyntax =
  match SimplExpr.transl_ps csyntax with
  | Errors.OK (p, g) ->
      Camlcoq.next_atom := g.SimplExpr.gen_next;
      p
  | Errors.Error msg ->
      Diagnostics.fatal_error ("can not convert", 0) "%a" Driveraux.print_error
        msg

let rec remove_skip = function
  | Clight.PSsequence (ps1, ps2) -> (
      match remove_skip ps1 with
      | Clight.PSskip -> remove_skip ps2
      | ps1 -> (
          match remove_skip ps2 with
          | Clight.PSskip -> ps1
          | ps2 -> Clight.PSsequence (ps1, ps2)))
  | Clight.PSfor (opt_init, opt_cond, opt_incr) ->
      Clight.PSfor
        (opt_map remove_skip opt_init, opt_cond, opt_map remove_skip opt_incr)
  | ps -> ps

type extra_info = AFuncDecl of string | VarDecls of string list | Nothing

let rec is_proto = function
  | Cabs.PROTO _ -> true
  | Cabs.PTR (_, t) -> is_proto t
  | _ -> false

let gen_extra_info ps =
  let get_name = function Cabs.Init_name (Cabs.Name (s, _, _, _), _) -> s in
  match ps with
  | Cabs.PDECL
      (Cabs.DECDEF ((_, [ Cabs.Init_name (Cabs.Name (fname, t, _, _), _) ]), _))
    when is_proto t ->
      AFuncDecl fname
  | Cabs.PDECL (Cabs.DECDEF ((_, init_names), _)) ->
      VarDecls (List.map get_name init_names)
  | _ -> Nothing

let parse_pstmt text =
  let ps = Parse.parse_ps_string "source" text in
  let extra_info = gen_extra_info ps in
  (ps, extra_info)

let clear_names names =
  List.iter (fun n -> Elab.env := Env.remove_name !Elab.env n) names

let transform_pstmt pv_names (ps, info) =
  let pv_names =
    match info with
    | AFuncDecl _ ->
        clear_names (SSet.elements pv_names);
        SSet.empty
    | VarDecls pvs -> SSet.union (SSet.of_list pvs) pv_names
    | _ -> pv_names
  in
  let ps = Elab.elab_ps_file ps in
  let pclight = convertPClight (C2C.convertPS !Elab.env ps) in
  let pclight = remove_skip pclight in
  ((pclight, info), pv_names)

let rec deseq = function
  | Clight.PSsequence (ps1, ps2) -> deseq ps1 @ deseq ps2
  | ps -> [ ps ]

let rec convert_pstmt f = function
  | Clight.PSassert a -> Clight.PSassert (f a)
  | Clight.PSbuiltin _ -> failwith "unsupported PSbuiltin"
  | Clight.PSfake _ -> failwith "unsupported PSfake"
  | Clight.PSsequence (ps1, ps2) ->
      Clight.PSsequence (convert_pstmt f ps1, convert_pstmt f ps2)
  | Clight.PSskip -> Clight.PSskip
  | Clight.PSassign (Clight.Evar (id, typ), e) ->
      Clight.PSset (id, var_to_temp e)
  | Clight.PSassign (e1, e2) -> Clight.PSassign (var_to_temp e1, var_to_temp e2)
  | Clight.PSset (id, e) -> Clight.PSset (id, var_to_temp e)
  | Clight.PScall (ret, f, args) ->
      Clight.PScall (ret, f, List.map var_to_temp args)
  | Clight.PSbreak -> Clight.PSbreak
  | Clight.PScontinue -> Clight.PScontinue
  | Clight.PSreturn ret -> Clight.PSreturn (opt_map var_to_temp ret)
  | Clight.PSwhile cond -> Clight.PSwhile (var_to_temp cond)
  | Clight.PSfor (opt_init, opt_cond, opt_incr) ->
      Clight.PSfor
        ( opt_map (convert_pstmt f) opt_init,
          opt_map var_to_temp opt_cond,
          opt_map (convert_pstmt f) opt_incr )
  | Clight.PSif cond -> Clight.PSif (var_to_temp cond)
  | Clight.PSelse -> Clight.PSelse
  | Clight.PSlbrace -> Clight.PSlbrace
  | Clight.PSrbrace -> Clight.PSrbrace
  | Clight.PSdecl decls -> Clight.PSdecl decls

type param = ident * Ctypes.coq_type

type rettyp = Ctypes.coq_type

type 'a func_info =
  | FuncDef of
      string * 'a Clight.partial_statement_with list * param list * rettyp
  | FuncDecl of string * 'a * param list * rettyp

let get_func_info st_einfo_pairs =
  let split_funcs_rev pairs =
    (* aux1: before funcdecl *)
    let rec aux1 temp = function
      | [] -> (temp, [])
      | (_, AFuncDecl _) :: _ as l -> (temp, l)
      | (ps, _) :: l -> aux1 (ps :: temp) l
    in
    let rec aux2 temp = function
      | (_, AFuncDecl name) :: l ->
          let psl, l = aux1 [] l in
          aux2 ((name, psl) :: temp) l
      | _ :: l -> aux2 temp l
      | [] -> temp
    in
    aux2 [] pairs
  in
  let rec split_lbrace rev_before = function
    | Clight.PSlbrace :: _ as l -> (rev_before, l)
    | ps :: l -> split_lbrace (ps :: rev_before) l
    | [] -> failwith "internal: split_lbrace"
  in
  let ps_decls_to_decls pstmts =
    List.concat
      (List.map
         (function
           | Clight.PSdecl decls -> decls
           | _ -> failwith "internal: ps_decls_to_decls")
         pstmts)
  in
  let process_fundecl name spec rev_decls =
    let rev_param_rets = ps_decls_to_decls rev_decls in
    match rev_param_rets with
    | [] -> FuncDecl (name, spec, [], Ctypes.Tvoid)
    | _ ->
        let last_ident, retty = List.hd rev_param_rets in
        let last_name = Hashtbl.find Camlcoq.string_of_atom last_ident in
        if last_name = "__return" then
          FuncDecl (name, spec, List.rev (List.tl rev_param_rets), retty)
        else FuncDecl (name, spec, List.rev rev_param_rets, Ctypes.Tvoid)
  in
  let process_fundef name rev_psl =
    let psl = List.rev rev_psl in
    let rev_param_rets, body = split_lbrace [] psl in
    let rev_param_rets = ps_decls_to_decls rev_param_rets in
    match rev_param_rets with
    | [] -> FuncDef (name, body, [], Ctypes.Tvoid)
    | _ ->
        let last_ident, retty = List.hd rev_param_rets in
        let last_name = Hashtbl.find Camlcoq.string_of_atom last_ident in
        if last_name = "__return" then
          FuncDef (name, body, List.rev (List.tl rev_param_rets), retty)
        else FuncDef (name, body, List.rev rev_param_rets, Ctypes.Tvoid)
  in
  let once (name, rev_psl) =
    match rev_psl with
    | Clight.PSskip :: Clight.PSassert a :: decls ->
        process_fundecl name a decls
    | _ -> process_fundef name rev_psl
  in
  let rev_funcs = split_funcs_rev st_einfo_pairs in
  List.map once rev_funcs

module AClightnorm = struct
  open Clight
  open AClight

  let gen_ident () =
    let id = !Camlcoq.next_atom in
    Camlcoq.next_atom := Camlcoq.P.succ id;
    id

  let rec norm_expr e =
    let sl, e' = norm_expr_1 e in
    if Clightnorm.accesses_memory e then
      let ty = typeof e in
      let id = gen_ident () in
      (sl @ [ Cset (id, e') ], Etempvar (id, ty))
    else (sl, e')

  and norm_expr_1 e =
    match e with
    | Econst_int _ | Econst_float _ | Econst_single _ | Econst_long _ -> ([], e)
    | Evar _ | Etempvar _ -> ([], e)
    | Ederef (e1, t) ->
        let sl, e1' = norm_expr e1 in
        (sl, Ederef (e1', t))
    | Eaddrof (e1, t) ->
        let sl, e1' = norm_expr_lvalue e1 in
        (sl, Eaddrof (e1', t))
    | Eunop (op, e1, t) ->
        let sl, e1' = norm_expr e1 in
        (sl, Eunop (op, e1', t))
    | Ebinop (op, e1, e2, t) ->
        let sl1, e1' = norm_expr e1 in
        let sl2, e2' = norm_expr e2 in
        (sl1 @ sl2, Ebinop (op, e1', e2', t))
    | Ecast (e1, t) ->
        let sl, e1' = norm_expr e1 in
        (sl, Ecast (e1', t))
    | Efield (e1, id, t) ->
        let sl, e1' = norm_expr e1 in
        (sl, Efield (e1', id, t))
    | Esizeof _ | Ealignof _ -> ([], e)

  and norm_expr_lvalue e = norm_expr_1 e

  let rec norm_expr_list el =
    match el with
    | [] -> ([], [])
    | e1 :: el ->
        let sl1, e1' = norm_expr e1 in
        let sl2, el' = norm_expr_list el in
        (sl1 @ sl2, e1' :: el')

  let rec add_sequence sl s =
    match sl with [] -> s | s1 :: sl -> Csequence (s1, add_sequence sl s)

  let rec norm_cstmt s =
    match s with
    | Cskip -> s
    | Cassign (e1, e2) ->
        let sl1, e1' = norm_expr_lvalue e1 in
        let sl2, e2' = norm_expr e2 in
        add_sequence (sl1 @ sl2) (Cassign (e1', e2'))
    | Cset (id, e) ->
        let sl, e' = norm_expr_lvalue e in
        add_sequence sl (Cset (id, e'))
    | Ccall (optid, e, el) ->
        let sl1, e' = norm_expr e in
        let sl2, el' = norm_expr_list el in
        add_sequence (sl1 @ sl2) (Ccall (optid, e', el'))
    | Csequence (s1, s2) -> Csequence (norm_cstmt s1, norm_cstmt s2)
    | Cifthenelse (e, s1, s2) ->
        let sl, e' = norm_expr e in
        add_sequence sl (Cifthenelse (e', norm_cstmt s1, norm_cstmt s2))
    | Cloop (s1, s2) -> Cloop (norm_cstmt s1, norm_cstmt s2)
    | Cbreak | Ccontinue | Creturn None -> s
    | Creturn (Some e) ->
        let sl, e' = norm_expr e in
        add_sequence sl (Creturn (Some e'))
    | Cassert _ -> s
    | Cexgiven (v, a, s) -> Cexgiven (v, a, norm_cstmt s)

  let norm_cfunction (Cfunc (frees, pre, post, body)) =
    Cfunc (frees, pre, post, norm_cstmt body)
end

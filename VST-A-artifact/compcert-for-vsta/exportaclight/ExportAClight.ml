open Format
open ExprvalDef
open PLSDef
open AClightLib
open AClight
open ATriple
open ExportClight

(* hack name_temporary
   try to generate the same name as clightgen 3.6 *)
let unnamed_temps : ident list ref = ref []

let name_temporary t =
  if not (Hashtbl.mem Camlcoq.string_of_atom t) then
    unnamed_temps := t :: !unnamed_temps

let name_temp_final () =
  let temps = List.sort_uniq Camlcoq.P.compare !unnamed_temps in
  List.iteri
    (fun i t -> Hashtbl.add temp_names t (sprintf "_t'%d" (i + 1)))
    temps;
  unnamed_temps := []

let name_opt_temporary = function None -> () | Some id -> name_temporary id

let rec name_cstmt stmt =
  match stmt with
  | Cassert _ | Cskip | Cbreak | Ccontinue | Creturn None -> ()
  | Cexgiven (_, _, s) -> name_cstmt s
  | Csequence (s1, s2) ->
      name_cstmt s1;
      name_cstmt s2
  | Cassign (e1, e2) ->
      name_expr e1;
      name_expr e2
  | Ccall (optid, e1, el) ->
      name_opt_temporary optid;
      name_expr e1;
      List.iter name_expr el
  | Cset (id, e) ->
      name_temporary id;
      name_expr e
  | Cifthenelse (e, s1, s2) ->
      name_expr e;
      name_cstmt s1;
      name_cstmt s2
  | Cloop (s1, s2) ->
      name_cstmt s1;
      name_cstmt s2
  | Creturn (Some e) -> name_expr e

let name_function = function
  | AClight.Cfunc (withs, pre, post, body) ->
      name_cstmt body;
      name_temp_final ()

let logical_name env id =
  match IDMap.find_opt id env.ident_to_bound with
  | Some (n, i) -> if i = 0 then n else n ^ "_" ^ string_of_int i
  | None -> (
      match IDMap.find_opt id env.logical_to_prog with
      | Some pv -> Hashtbl.find Camlcoq.string_of_atom pv
      | None -> IDMap.find id env.name_of_free)

let logical_var env p id = fprintf p "%s" (logical_name env id)

(* separated_iter f g [x1; x2; ...; xn] =
 *   f x1; g(); f x2; g(); ...; g(); f xn
 *)
let rec separated_iter f g = function
  | [] -> ()
  | [ x ] -> f x
  | x :: xs ->
      f x;
      g ();
      separated_iter f g xs

let string_of_bop = function
  | Oadd -> "Z.add"
  | Osub -> "Z.sub"
  | Omul -> "Z.mul"
  | Odiv -> "Z.div"
  | Omod -> "Z.rem"
  | Ocons -> "cons"
  | Oapp -> "app"

let coqname p s =
  let s = Camlcoq.camlstring_of_coqstring s in
  fprintf p "%s" s

let rec expr_val env p = function
  | Vunit -> fprintf p "tt"
  | Vint n -> coqZ p n
  | Vvar id -> logical_var env p id
  | Vpair (v1, v2) -> fprintf p "(%a, %a)" (expr_val env) v1 (expr_val env) v2
  | Vfapp (f, args) -> fprintf p "(%a %a)" coqname f (func_args env) args
  | Vuop v -> fprintf p "(Z.sub 0 %a)" (expr_val env) v
  | Vbop (op, v1, v2) ->
      fprintf p "(%s %a %a)" (string_of_bop op) (expr_val env) v1 (expr_val env)
        v2
  | Vfield_addr (v, comptyp, field) ->
      let fldtype =
        match comptyp with
        | Ctypes.Tstruct _ -> "StructField"
        | Ctypes.Tunion _ -> "UnionField"
        | _ -> failwith "unreachable"
      in
      fprintf p "(field_address %a [%s %a] %a)" typ comptyp fldtype ident field
        (expr_val env) v

and func_args env p = separated_iter (expr_val env p) (fun () -> fprintf p " ")

let rec proposition env p = function
  | TT -> fprintf p "True"
  | FF -> fprintf p "False"
  | Pvle (v1, v2) ->
      fprintf p "(Z.le %a %a)" (expr_val env) v1 (expr_val env) v2
  | Pvge (v1, v2) ->
      fprintf p "(Z.ge %a %a)" (expr_val env) v1 (expr_val env) v2
  | Pvlt (v1, v2) ->
      fprintf p "(Z.lt %a %a)" (expr_val env) v1 (expr_val env) v2
  | Pvgt (v1, v2) ->
      fprintf p "(Z.gt %a %a)" (expr_val env) v1 (expr_val env) v2
  | Pveq (v1, v2) -> fprintf p "(%a = %a)" (expr_val env) v1 (expr_val env) v2
  | Pnot prop -> fprintf p "(not %a)" (proposition env) prop
  | Pand (prop1, prop2) ->
      fprintf p "(%a /\\@ %a)" (proposition env) prop1 (proposition env) prop2
  | Pforall (id, prop) ->
      fprintf p "(forall %a,@ %a)" (logical_var env) id (proposition env) prop
  | Pexists (id, prop) ->
      fprintf p "(exists %a,@ %a)" (logical_var env) id (proposition env) prop
  | Ppred (name, args) -> fprintf p "(%a %a)" coqname name (func_args env) args

let local env p = function
  | Temp (id, v) -> fprintf p "temp %a %a" ident id (expr_val env) v

let rec separation env p = function
  | Emp -> fprintf p "emp"
  | Data_at (t, v1, v2) ->
      fprintf p "(data_at Tsh %a %a %a)" typ t (expr_val env) v1 (expr_val env)
        v2
  | Wand (s1, s2) ->
      fprintf p "(wand %a %a)" (separation env) s1 (separation env) s2
  | Spred (name, args) -> fprintf p "(%a %a)" coqname name (func_args env) args

let semic_separated format p =
  separated_iter (fun x -> fprintf p "%a" format x) (fun () -> fprintf p "; ")

let triple env p (props, locals, seps) =
  fprintf p "(PROP (%a)@ LOCAL (%a)@ SEP (%a))"
    (semic_separated (proposition env))
    props
    (semic_separated (local env))
    locals
    (semic_separated (separation env))
    seps

let rec extract_exs = function
  | Anormal (props, locals, seps) -> ([], (props, locals, seps))
  | Aex (id, a) ->
      let exs, pls = extract_exs a in
      (id :: exs, pls)

let assertion env p a =
  let exs, pls = extract_exs a in
  match exs with
  | [] -> triple env p pls
  | _ ->
      fprintf p "@[<v 2>(EX ";
      separated_iter
        (fun id -> (logical_var env) p id)
        (fun () -> fprintf p " ")
        exs;
      fprintf p ",@ ";
      fprintf p "%a" (triple env) pls;
      fprintf p ")%%assert@]"

let rec cstmt env p = function
  | Cskip -> fprintf p "Cskip"
  | Cassign (e1, e2) -> fprintf p "@[<hov 2>(Cassign@ %a@ %a)@]" expr e1 expr e2
  | Cset (id, e) -> fprintf p "@[<hov 2>(Cset %a@ %a)@]" ident id expr e
  | Ccall (ret, f, args) ->
      fprintf p "@[<hov 2>(Ccall %a@ %a@ %a)@]" (print_option ident) ret expr f
        (print_list expr) args
  | Csequence (s1, s2) ->
      fprintf p "@[<hv 2>(Csequence@ %a@ %a)@]" (cstmt env) s1 (cstmt env) s2
  | Cifthenelse (cond, s1, s2) ->
      fprintf p "@[<hv 2>(Cifthenelse %a@ %a@ %a)@]" expr cond (cstmt env) s1
        (cstmt env) s2
  | Cloop (s1, s2) ->
      fprintf p "@[<hv 2>(Cloop@ %a@ %a)@]" (cstmt env) s1 (cstmt env) s2
  | Cbreak -> fprintf p "Cbreak"
  | Ccontinue -> fprintf p "Ccontinue"
  | Creturn e -> fprintf p "@[<hv 2>(Creturn %a)@]" (print_option expr) e
  | Cassert a -> fprintf p "@[<hv 2>(Cassert@ %a)@]" (assertion env) a
  | Cexgiven (given, a, st) ->
      fprintf p "@[<hv 2>(EXGIVEN %a@ [[%a]]@ %a)@]" (logical_var env) given
        (assertion env) a (cstmt env) st

let lift_pre_exs env (Cfunc (withs, pre, post, body)) =
  let gen_pre_ex_lift env id =
    let name = logical_name env id in
    gen_free_ident env (name ^ "\'")
  in
  let pre_exs, (props, locals, seps) = extract_exs pre in
  let lifted_withs, env = map_accum_l gen_pre_ex_lift env pre_exs in
  let renames = List.combine pre_exs lifted_withs in
  let withs = withs @ lifted_withs in
  let props =
    List.map
      (fun p ->
        List.fold_left
          (fun p (id, id') -> ATriple.Rename.rename_prop id id' p)
          p renames)
      props
  in
  let locals =
    List.map
      (fun l ->
        List.fold_left
          (fun l (id, id') -> ATriple.Rename.rename_local id id' l)
          l renames)
      locals
  in
  let seps =
    List.map
      (fun s ->
        List.fold_left
          (fun s (id, id') -> ATriple.Rename.rename_sep id id' s)
          s renames)
      seps
  in
  let pre = PLSDef.Anormal (props, locals, seps) in
  (env, Cfunc (withs, pre, post, body))

let funcspec env p (withs, pre, post) =
  let logicals p =
    separated_iter (logical_var env p) (fun () -> fprintf p " ")
  in
  (match withs with
  | [] -> fprintf p "ANNOTATION_WITH (_: unit), @ "
  | _ -> fprintf p "ANNOTATION_WITH %a,@ " logicals withs);
  fprintf p "(%a,@ %a)" (assertion env) pre (assertion env) post

module ForDecl = struct
  (* always print positive except __return in local *)
  let decl_ident p id =
    match Hashtbl.find_opt Camlcoq.string_of_atom id with
    | Some "__return" -> fprintf p "___return"
    | _ -> fprintf p "%ld%%positive" (Camlcoq.P.to_int32 id)

  let local env p = function
    | Temp (id, v) -> fprintf p "temp %a %a" decl_ident id (expr_val env) v

  let triple env p (props, locals, seps) =
    fprintf p "(PROP (%a)@ LOCAL (%a)@ SEP (%a))"
      (semic_separated (proposition env))
      props
      (semic_separated (local env))
      locals
      (semic_separated (separation env))
      seps

  let assertion env p a =
    let exs, pls = extract_exs a in
    match exs with
    | [] -> triple env p pls
    | _ ->
        fprintf p "@[<v 2>(EX ";
        separated_iter
          (fun id -> (logical_var env) p id)
          (fun () -> fprintf p " ")
          exs;
        fprintf p ",@ ";
        fprintf p "%a" (triple env) pls;
        fprintf p ")%%assert@]"

  let funcspec env p (withs, pre, post) =
    let logicals p =
      separated_iter (logical_var env p) (fun () -> fprintf p " ")
    in
    let pre_exs, (props, locals, seps) = extract_exs pre in
    let withs = withs @ pre_exs in
    let pre = PLSDef.Anormal (props, locals, seps) in
    (match withs with
    | [] -> fprintf p "ANNOTATION_WITH (_: unit), @ "
    | _ -> fprintf p "ANNOTATION_WITH %a,@ " logicals withs);
    fprintf p "(%a,@ %a)" (assertion env) pre (assertion env) post
end

let rec extract_full_path = function
  | Coq_mk_full_path (pre, path, post) -> ([], pre, path, post)
  | Coq_bind_full_path (ex, full_p) ->
      let exs, pre, path, post = extract_full_path full_p in
      (ex :: exs, pre, path, post)

let rec extract_full_ret_path = function
  | Coq_mk_full_ret_path (pre, path, ret, post) -> ([], pre, path, ret, post)
  | Coq_bind_full_ret_path (ex, full_p) ->
      let exs, pre, path, ret, post = extract_full_ret_path full_p in
      (ex :: exs, pre, path, ret, post)

let atom_to_stmt = function
  | Askip -> Clight.Sskip
  | Aassign (e1, e2) -> Clight.Sassign (e1, e2)
  | Aset (id, e) -> Clight.Sset (id, e)
  | Acall (ret, f, args) -> Clight.Scall (ret, f, args)

let rec path_to_stmt p tail =
  match p with
  | [] -> tail
  | Datatypes.Coq_inl (true, e) :: p' ->
      Clight.Ssequence
        ( Clight.Sifthenelse (e, Clight.Sskip, Clight.Sbreak),
          path_to_stmt p' tail )
  | Datatypes.Coq_inl (false, e) :: p' ->
      Clight.Ssequence
        ( Clight.Sifthenelse (e, Clight.Sbreak, Clight.Sskip),
          path_to_stmt p' tail )
  | Datatypes.Coq_inr s :: p' ->
      Clight.Ssequence (atom_to_stmt s, path_to_stmt p' tail)

let rec frees_in_expr_val bounded = function
  | Vunit | Vint _ -> IDSet.empty
  | Vvar id -> if IDSet.mem id bounded then IDSet.empty else IDSet.singleton id
  | Vuop v | Vfield_addr (v, _, _) -> frees_in_expr_val bounded v
  | Vbop (_, v1, v2) ->
      IDSet.union (frees_in_expr_val bounded v1) (frees_in_expr_val bounded v2)
  | Vpair (v1, v2) ->
      IDSet.union (frees_in_expr_val bounded v1) (frees_in_expr_val bounded v2)
  | Vfapp (_, vs) ->
      List.fold_left
        (fun acc v -> IDSet.union acc (frees_in_expr_val bounded v))
        IDSet.empty vs

let rec frees_in_prop bounded = function
  | TT | FF -> IDSet.empty
  | Pnot p -> frees_in_prop bounded p
  | Pand (p1, p2) ->
      IDSet.union (frees_in_prop bounded p1) (frees_in_prop bounded p2)
  | Pvle (v1, v2) | Pvge (v1, v2) | Pvlt (v1, v2) | Pvgt (v1, v2) | Pveq (v1, v2)
    ->
      IDSet.union (frees_in_expr_val bounded v1) (frees_in_expr_val bounded v2)
  | Pforall (id, p) | Pexists (id, p) -> frees_in_prop (IDSet.add id bounded) p
  | Ppred (_, vs) ->
      List.fold_left
        (fun acc v -> IDSet.union acc (frees_in_expr_val bounded v))
        IDSet.empty vs

let rec frees_in_sep bounded = function
  | Emp -> IDSet.empty
  | Data_at (_, v1, v2) ->
      IDSet.union (frees_in_expr_val bounded v1) (frees_in_expr_val bounded v2)
  | Wand (s1, s2) ->
      IDSet.union (frees_in_sep bounded s1) (frees_in_sep bounded s2)
  | Spred (_, vs) ->
      List.fold_left
        (fun acc v -> IDSet.union acc (frees_in_expr_val bounded v))
        IDSet.empty vs

let frees_in_assertion a =
  let exs, (props, _, seps) = extract_exs a in
  let bounded = IDSet.of_list exs in
  let prop_frees =
    List.fold_left
      (fun acc v -> IDSet.union acc (frees_in_prop bounded v))
      IDSet.empty props
  in
  let sep_frees =
    List.fold_left
      (fun acc v -> IDSet.union acc (frees_in_sep bounded v))
      IDSet.empty seps
  in
  IDSet.union prop_frees sep_frees

let full_path (func_name, env) p full_path =
  let frees, pre, path, post = extract_full_path full_path in
  let path_stmt = path_to_stmt path Clight.Sskip in
  let frees =
    IDSet.inter (IDSet.of_list frees)
      (IDSet.union (frees_in_assertion pre) (frees_in_assertion post))
  in
  let frees = IDSet.elements frees in
  let logicals p =
    separated_iter (logical_var env p) (fun () -> fprintf p " ")
  in
  fprintf p "@[<v 0>";
  fprintf p "forall (Espec: OracleKind) %a,@ " logicals frees;
  fprintf p "let Delta_specs := Delta_specs_%s in@ " func_name;
  fprintf p "let Delta := Delta_%s Delta_specs in@ " func_name;
  fprintf p "semax Delta %a@ %a@ (normal_split_assert@ %a)" (assertion env) pre
    stmt path_stmt (assertion env) post;
  fprintf p "@]"

let full_normal_exit_path (func_name, env) p full_path =
  let frees, pre, path, post = extract_full_path full_path in
  let path_stmt = path_to_stmt path Clight.Sskip in
  let frees =
    IDSet.inter (IDSet.of_list frees)
      (IDSet.union (frees_in_assertion pre) (frees_in_assertion post))
  in
  let frees = IDSet.elements frees in
  let logicals p =
    separated_iter (logical_var env p) (fun () -> fprintf p " ")
  in
  fprintf p "@[<v 0>";
  fprintf p "forall (Espec: OracleKind) %a,@ " logicals frees;
  fprintf p "let Delta_specs := Delta_specs_%s in@ " func_name;
  fprintf p "let Delta := Delta_%s Delta_specs in@ " func_name;
  fprintf p
    "semax Delta %a@ %a@ (normal_split_assert (RA_normal (frame_ret_assert \
     (function_body_ret_assert tvoid %a) (stackframe_of f_%s))))"
    (assertion env) pre stmt path_stmt (assertion env) post func_name;
  fprintf p "@]"

let full_ret_path (func_name, rettyp, env) p full_ret_path =
  let frees, pre, path, ret, post = extract_full_ret_path full_ret_path in
  let path_stmt = path_to_stmt path (Clight.Sreturn ret) in
  let frees =
    IDSet.inter (IDSet.of_list frees)
      (IDSet.union (frees_in_assertion pre) (frees_in_assertion post))
  in
  let frees = IDSet.elements frees in
  let logicals p =
    separated_iter (logical_var env p) (fun () -> fprintf p " ")
  in
  fprintf p "@[<v 0>";
  fprintf p "forall (Espec: OracleKind) %a,@ " logicals frees;
  fprintf p "let Delta_specs := Delta_specs_%s in@ " func_name;
  fprintf p "let Delta := Delta_%s Delta_specs in@ " func_name;
  fprintf p
    "semax Delta %a@ %a@ (return_split_assert (RA_return (frame_ret_assert \
     (function_body_ret_assert %a %a) (stackframe_of f_%s))))"
    (assertion env) pre stmt path_stmt typ rettyp (assertion env) post func_name;
  fprintf p "@]"

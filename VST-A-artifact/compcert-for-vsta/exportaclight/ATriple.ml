open ExprvalDef
open PLSDef
open AClightLib
open AAst
open AClight

exception Unreachable

exception Invalid_assertion

module BVMap = Map.Make (struct
  type t = string * int

  let compare = compare
end)

let next_bound bounds n =
  let new_bound =
    match SMap.find_opt n bounds with None -> 0 | Some i -> i + 1
  in
  (SMap.add n new_bound bounds, new_bound)

let rec rename_cstmt n i = function
  | Cassert a -> Cassert (rename_a n i a)
  | Cexgiven (n', a, st) ->
      if n = n' then Cexgiven (n', a, st)
      else Cexgiven (n', rename_a n i a, rename_cstmt n i st)
  | Csequence (st1, st2) ->
      Csequence (rename_cstmt n i st1, rename_cstmt n i st2)
  | Cifthenelse (cond, st1, st2) ->
      Cifthenelse (cond, rename_cstmt n i st1, rename_cstmt n i st2)
  | Cloop (st1, st2) -> Cloop (rename_cstmt n i st1, rename_cstmt n i st2)
  | st -> st

let rec a_rename_logical b = function
  | Forall (FreeV n, a) ->
      let b1, i = next_bound b n in
      let a = rename_a n i a in
      let b2, a = a_rename_logical b1 a in
      (b2, Forall (BoundV (n, i), a))
  | Exists (FreeV n, a) ->
      let b1, i = next_bound b n in
      let a = rename_a n i a in
      let b2, a = a_rename_logical b1 a in
      (b2, Exists (BoundV (n, i), a))
  | And (a1, a2) ->
      let b1, a1 = a_rename_logical b a1 in
      let b2, a2 = a_rename_logical b1 a2 in
      (b2, And (a1, a2))
  | Not a ->
      let b1, a = a_rename_logical b a in
      (b1, Not a)
  | SepConj (a1, a2) ->
      let b1, a1 = a_rename_logical b a1 in
      let b2, a2 = a_rename_logical b1 a2 in
      (b2, SepConj (a1, a2))
  | Forall (v, a) ->
      let b1, a = a_rename_logical b a in
      (b1, Forall (v, a))
  | Exists (v, a) ->
      let b1, a = a_rename_logical b a in
      (b1, Exists (v, a))
  | a -> (SMap.empty, a)

let rec cstmt_rename_logical b = function
  | Cassert a ->
      let _, a = a_rename_logical b a in
      Cassert a
  | Cexgiven (given, a, st) ->
      let b1, i = next_bound b given in
      let a = rename_a given i a in
      let st = rename_cstmt given i st in
      let _, a = a_rename_logical b1 a in
      let st = cstmt_rename_logical b1 st in
      Cexgiven ((given, i), a, st)
  | Csequence (st1, st2) ->
      let st1 = cstmt_rename_logical b st1 in
      let st2 = cstmt_rename_logical b st2 in
      Csequence (st1, st2)
  | Cifthenelse (cond, st1, st2) ->
      let st1 = cstmt_rename_logical b st1 in
      let st2 = cstmt_rename_logical b st2 in
      Cifthenelse (cond, st1, st2)
  | Cloop (st1, st2) ->
      let st1 = cstmt_rename_logical b st1 in
      let st2 = cstmt_rename_logical b st2 in
      Cloop (st1, st2)
  (* make the typechecker happy *)
  | Cskip -> Cskip
  | Cassign (e1, e2) -> Cassign (e1, e2)
  | Ccall (ret, f, args) -> Ccall (ret, f, args)
  | Cset (id, e) -> Cset (id, e)
  | Cbreak -> Cbreak
  | Ccontinue -> Ccontinue
  | Creturn ret -> Creturn ret

let rec cstmt_exist_lift = function
  | Cassert a -> Cassert (exists_lift a)
  | Cexgiven (given, a, st) ->
      let a = exists_lift a in
      let st = cstmt_exist_lift st in
      Cexgiven (given, a, st)
  | Csequence (st1, st2) ->
      let st1 = cstmt_exist_lift st1 in
      let st2 = cstmt_exist_lift st2 in
      Csequence (st1, st2)
  | Cifthenelse (cond, st1, st2) ->
      let st1 = cstmt_exist_lift st1 in
      let st2 = cstmt_exist_lift st2 in
      Cifthenelse (cond, st1, st2)
  | Cloop (st1, st2) ->
      let st1 = cstmt_exist_lift st1 in
      let st2 = cstmt_exist_lift st2 in
      Cloop (st1, st2)
  (* make the typechecker happy *)
  | Cskip -> Cskip
  | Cassign (e1, e2) -> Cassign (e1, e2)
  | Ccall (ret, f, args) -> Ccall (ret, f, args)
  | Cset (id, e) -> Cset (id, e)
  | Cbreak -> Cbreak
  | Ccontinue -> Ccontinue
  | Creturn ret -> Creturn ret

let gen_ident () =
  let id = !Camlcoq.next_atom in
  Camlcoq.next_atom := Camlcoq.P.succ id;
  id

type pls_gen_env = {
  freevars : AST.ident SMap.t;
  (* global *)
  name_of_free : string IDMap.t;
  (* global *)
  prog_to_logical : AST.ident IDMap.t;
  (* global *)
  logical_to_prog : AST.ident IDMap.t;
  (* global *)
  bound_to_ident : AST.ident BVMap.t;
  (* global *)
  ident_to_bound : (string * int) IDMap.t;
  (* global *)
  appeared_pvs : AST.ident list; (* per assertion *)
}

let empty_gen_env =
  {
    freevars = SMap.empty;
    name_of_free = IDMap.empty;
    prog_to_logical = IDMap.empty;
    logical_to_prog = IDMap.empty;
    bound_to_ident = BVMap.empty;
    ident_to_bound = IDMap.empty;
    appeared_pvs = [];
  }

let gen_free_ident env name =
  let id = gen_ident () in
  ( id,
    {
      env with
      freevars = SMap.add name id env.freevars;
      name_of_free = IDMap.add id name env.name_of_free;
    } )

let add_progv env id = { env with appeared_pvs = id :: env.appeared_pvs }

let assertion_end env = { env with appeared_pvs = [] }

let logical_of_prog env pid =
  let p2l = env.prog_to_logical in
  let l2p = env.logical_to_prog in
  match IDMap.find_opt pid p2l with
  | Some lid -> (lid, env)
  | None ->
      let lid = gen_ident () in
      ( lid,
        {
          env with
          prog_to_logical = IDMap.add pid lid p2l;
          logical_to_prog = IDMap.add lid pid l2p;
        } )

let ident_of_bound env (n, i) =
  let b2i = env.bound_to_ident in
  let i2b = env.ident_to_bound in
  match BVMap.find_opt (n, i) b2i with
  | Some id -> (id, env)
  | None ->
      let id = gen_ident () in
      ( id,
        {
          env with
          bound_to_ident = BVMap.add (n, i) id b2i;
          ident_to_bound = IDMap.add id (n, i) i2b;
        } )

(* let convert_uop = function
   | Neg -> Oneg *)

let convert_bop = function
  | Add -> Oadd
  | Sub -> Osub
  | Mul -> Omul
  | Div -> Odiv
  | Mod -> Omod
  | Cons -> Ocons
  | Append -> Oapp

let value_macro_map =
  List.fold_left
    (fun s (name, coqname) ->
      SMap.add name (Camlcoq.coqstring_of_camlstring coqname) s)
    SMap.empty
    [
      ("NULL", "nullval");
      ("INT_MIN", "Int.min_signed");
      ("INT_MAX", "Int.max_signed");
      ("UINT_MAX", "Int.max_unsigned");
      ("nil", "nil");
    ]

let comp_typ_of_field field =
  let comps = Maps.PTree.elements !C2C.comp_env in
  let tid, comp =
    List.find
      (fun (_, comp) ->
        List.exists (function id, _ -> id = field) comp.Ctypes.co_members)
      comps
  in
  match comp.Ctypes.co_su with
  | Ctypes.Struct -> Ctypes.Tstruct (tid, Ctypes.noattr)
  | Ctypes.Union -> Ctypes.Tunion (tid, Ctypes.noattr)

let comp_typ_of_ident typname =
  let comps = Maps.PTree.elements !C2C.comp_env in
  let tid, comp = List.find (fun (id, comp) -> id = typname) comps in
  match comp.Ctypes.co_su with
  | Ctypes.Struct -> Ctypes.Tstruct (tid, Ctypes.noattr)
  | Ctypes.Union -> Ctypes.Tunion (tid, Ctypes.noattr)

let rec val_to_expr_val env = function
  | VLiteral (LInt n) -> (Vint (Camlcoq.Z.of_sint n), env)
  | VVar (FreeV v_name) -> (
      match SMap.find_opt v_name value_macro_map with
      | Some coqname -> (Vfapp (coqname, []), env)
      | None -> (
          match SMap.find_opt v_name env.freevars with
          | Some fv -> (Vvar fv, env)
          | None ->
              let pv = hashtbl_find_exn Camlcoq.atom_of_string v_name in
              let id, env1 = logical_of_prog env pv in
              let env2 = add_progv env1 pv in
              (Vvar id, env2)))
  | VVar (BoundV (n, i)) ->
      let id, env1 = ident_of_bound env (n, i) in
      (Vvar id, env1)
  | VBinop (op, v1, v2) ->
      let v1, env1 = val_to_expr_val env v1 in
      let v2, env2 = val_to_expr_val env1 v2 in
      (Vbop (convert_bop op, v1, v2), env2)
  | VUop (op, v) ->
      let v, env1 = val_to_expr_val env v in
      (Vuop v, env1)
  | VTuple eles ->
      let eles, env1 = map_accum_l val_to_expr_val env eles in
      let rec aux = function
        | [] -> Vunit
        | [ x ] -> x
        | [ x; y ] -> Vpair (x, y)
        | x :: xs -> Vpair (x, aux xs)
      in
      (aux eles, env1)
  | VFApp (f_name, args) ->
      if f_name = "field_addr" then
        match args with
        | [ v; VVar (FreeV field) ] ->
            let field = hashtbl_find_exn Camlcoq.atom_of_string field in
            let v, env1 = val_to_expr_val env v in
            let comptyp = comp_typ_of_field field in
            (Vfield_addr (v, comptyp, field), env1)
        | [ v; VVar (FreeV typname); VVar (FreeV field) ] ->
            let field = hashtbl_find_exn Camlcoq.atom_of_string field in
            let typname = hashtbl_find_exn Camlcoq.atom_of_string typname in
            let v, env1 = val_to_expr_val env v in
            let comptyp = comp_typ_of_ident typname in
            (Vfield_addr (v, comptyp, field), env1)
        | _ -> raise Invalid_assertion
      else
        let args, env1 = map_accum_l val_to_expr_val env args in
        (Vfapp (Camlcoq.coqstring_of_camlstring f_name, args), env1)

let rec sep_to_list = function
  | SepConj (a1, a2) -> sep_to_list a1 @ sep_to_list a2
  | a -> [ a ]

let rec and_to_list = function
  | And (a1, a2) -> and_to_list a1 @ and_to_list a2
  | a -> [ a ]

let rec to_prop env = function
  | Forall (BoundV (n, i), a) ->
      let id, env1 = ident_of_bound env (n, i) in
      let p, env2 = to_prop env a in
      (Pforall (id, p), env2)
  | Exists (BoundV (n, i), a) ->
      let id, env1 = ident_of_bound env (n, i) in
      let p, env2 = to_prop env a in
      (Pexists (id, p), env2)
  | Proposition p_name ->
      if p_name = "True" then (TT, env)
      else if p_name = "False" then (FF, env)
      else raise Invalid_assertion
  | Relation (rel, v1, v2) ->
      let v1, env1 = val_to_expr_val env v1 in
      let v2, env2 = val_to_expr_val env1 v2 in
      let p =
        match rel with
        | Eq -> Pveq (v1, v2)
        | Ne -> Pnot (Pveq (v1, v2))
        | Ge -> Pvge (v1, v2)
        | Le -> Pvle (v1, v2)
        | Gt -> Pvgt (v1, v2)
        | Lt -> Pvlt (v1, v2)
      in
      (p, env2)
  | Predicate (p_name, args) ->
      let args, env1 = map_accum_l val_to_expr_val env args in
      (Ppred (Camlcoq.coqstring_of_camlstring p_name, args), env1)
  | Not a ->
      let p, env1 = to_prop env a in
      (Pnot p, env1)
  | And (a1, a2) ->
      let p1, env1 = to_prop env a1 in
      let p2, env2 = to_prop env1 a2 in
      (Pand (p1, p2), env2)
  | Forall (FreeV _, _) | Exists (FreeV _, _) | SepConj _ | SepImpl _ ->
      raise Invalid_assertion

(* suppose prop here *)

let rec to_sep env = function
  | Proposition p_name ->
      if p_name = "emp" then (Emp, env) else raise Invalid_assertion
  | Predicate (p_name, args) ->
      let args, env1 = map_accum_l val_to_expr_val env args in
      (Spred (Camlcoq.coqstring_of_camlstring p_name, args), env1)
  | SepImpl (a1, a2) ->
      let a1, env1 = to_sep env a1 in
      let a2, env2 = to_sep env1 a2 in
      (Wand (a1, a2), env2)
  | _ -> raise Invalid_assertion

let rm_tt = List.filter (function TT -> false | _ -> true)

let must_bound = function
  | BoundV (n, i) -> (n, i)
  | _ -> raise Invalid_assertion

let to_triple_explicit_ex env a =
  let exs, a = a in
  let ex_bounds = List.map must_bound exs in
  let ex_idents, env1 = map_accum_l ident_of_bound env ex_bounds in
  match List.rev (and_to_list a) with
  | [] -> (ex_idents, Anormal ([], [], []), env1)
  | sep :: props ->
      let props, env2 = map_accum_l to_prop env1 props in
      let seps, env3 = map_accum_l to_sep env2 (sep_to_list sep) in
      let appeared_pvs = env3.appeared_pvs in
      let appeared_pvs = List.sort_uniq Camlcoq.P.compare appeared_pvs in
      let appeared_pvids =
        List.map (fun v -> IDMap.find v env3.prog_to_logical) appeared_pvs
      in
      let locals =
        List.map
          (fun (pv, id) -> Temp (pv, Vvar id))
          (List.combine appeared_pvs appeared_pvids)
      in
      let env4 = assertion_end env3 in
      (ex_idents @ appeared_pvids, Anormal (props, locals, seps), env4)

let to_triple env a =
  let ex_idents, a, env1 = to_triple_explicit_ex env a in
  let a = List.fold_right (fun id a -> Aex (id, a)) ex_idents a in
  (a, env1)

let rec cstmt_transform env = function
  | Cassert a ->
      let a, env1 = to_triple env a in
      (Cassert a, env1)
  | Cexgiven ((n, i), a, st) ->
      let id, env1 = ident_of_bound env (n, i) in
      let a, env2 = to_triple env1 a in
      let st, env3 = cstmt_transform env2 st in
      (Cexgiven (id, a, st), env3)
  | Csequence (st1, st2) ->
      let st1, env1 = cstmt_transform env st1 in
      let st2, env2 = cstmt_transform env1 st2 in
      (Csequence (st1, st2), env2)
  | Cifthenelse (cond, st1, st2) ->
      let st1, env1 = cstmt_transform env st1 in
      let st2, env2 = cstmt_transform env1 st2 in
      (Cifthenelse (cond, st1, st2), env2)
  | Cloop (st1, st2) ->
      let st1, env1 = cstmt_transform env st1 in
      let st2, env2 = cstmt_transform env1 st2 in
      (Cloop (st1, st2), env2)
  (* make the typechecker happy *)
  | Cskip -> (Cskip, env)
  | Cassign (e1, e2) -> (Cassign (e1, e2), env)
  | Ccall (ret, f, args) -> (Ccall (ret, f, args), env)
  | Cset (id, e) -> (Cset (id, e), env)
  | Cbreak -> (Cbreak, env)
  | Ccontinue -> (Ccontinue, env)
  | Creturn ret -> (Creturn ret, env)

let driver_decl name spec =
  match AParse.parse_assertion spec with
  | AClight.Funcspec (withs, pre, post) ->
      let env =
        List.fold_left (fun e s -> snd (gen_free_ident e s)) empty_gen_env withs
      in
      let _, pre = a_rename_logical SMap.empty pre in
      let _, post = a_rename_logical SMap.empty post in
      let pre = exists_lift pre in
      let post = exists_lift post in
      let pre, env1 = to_triple env pre in
      let post, env2 = to_triple env1 post in
      let withs = SMap.fold (fun _ id l -> id :: l) env2.freevars [] in
      (withs, pre, post, env2)
  | _ -> failwith ("Not a function spec: " ^ name)

let driver (Cfunc (withs, pre, post, body)) =
  let env =
    List.fold_left (fun e s -> snd (gen_free_ident e s)) empty_gen_env withs
  in
  let _, pre = a_rename_logical SMap.empty pre in
  let _, post = a_rename_logical SMap.empty post in
  let pre = exists_lift pre in
  let post = exists_lift post in
  let pre, env1 = to_triple env pre in
  let post, env2 = to_triple env1 post in
  let renamed = cstmt_rename_logical SMap.empty body in
  let lifted = cstmt_exist_lift renamed in
  let body, env3 = cstmt_transform env2 lifted in
  let withs = SMap.fold (fun _ id l -> id :: l) env3.freevars [] in
  (Cfunc (withs, pre, post, body), env3)

module Rename = struct
  let rec rename_expr_val id id' = function
    | Vvar id1 when Camlcoq.P.eq id id1 -> Vvar id'
    | Vuop e -> Vuop (rename_expr_val id id' e)
    | Vbop (op, e1, e2) ->
        Vbop (op, rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Vpair (e1, e2) ->
        Vpair (rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Vfield_addr (e, typ, fld) ->
        Vfield_addr (rename_expr_val id id' e, typ, fld)
    | Vfapp (f, args) -> Vfapp (f, List.map (rename_expr_val id id') args)
    | e -> e

  let rec rename_prop id id' = function
    | TT -> TT
    | FF -> FF
    | Pnot p -> Pnot (rename_prop id id' p)
    | Pand (p1, p2) -> Pand (rename_prop id id' p1, rename_prop id id' p2)
    | Pvle (e1, e2) ->
        Pvle (rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Pvge (e1, e2) ->
        Pvge (rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Pvlt (e1, e2) ->
        Pvlt (rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Pvgt (e1, e2) ->
        Pvgt (rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Pveq (e1, e2) ->
        Pveq (rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Ppred (f, args) -> Ppred (f, List.map (rename_expr_val id id') args)
    | Pforall (id1, p) ->
        if Camlcoq.P.eq id id1 then Pforall (id1, p)
        else Pforall (id1, rename_prop id id' p)
    | Pexists (id1, p) ->
        if Camlcoq.P.eq id id1 then Pexists (id1, p)
        else Pexists (id1, rename_prop id id' p)

  let rename_local id id' = function
    | Temp (id1, e) -> Temp (id1, rename_expr_val id id' e)

  let rec rename_sep id id' = function
    | Emp -> Emp
    | Data_at (typ, e1, e2) ->
        Data_at (typ, rename_expr_val id id' e1, rename_expr_val id id' e2)
    | Spred (f, args) -> Spred (f, List.map (rename_expr_val id id') args)
    | Wand (s1, s2) -> Wand (rename_sep id id' s1, rename_sep id id' s2)
end

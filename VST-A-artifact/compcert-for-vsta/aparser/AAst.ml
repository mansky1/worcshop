open Aabs

type var = FreeV of string | BoundV of string * int

type value =
  | VLiteral of literal
  | VVar of var
  | VBinop of binop * value * value
  | VUop of uop * value
  | VTuple of value list
  | VFApp of string * value list

and literal = LInt of int

and binop = Add | Sub | Mul | Div | Mod | Cons | Append

and uop = Neg

type assertion =
  | Forall of var * assertion
  | Exists of var * assertion
  | Proposition of string
  | Relation of relation * value * value
  | Predicate of string * value list
  | And of assertion * assertion
  | Not of assertion
  | SepConj of assertion * assertion
  | SepImpl of assertion * assertion

and relation = Eq | Ne | Ge | Le | Gt | Lt

module Gen = struct
  let forall v a = Forall (v, a)

  let exists v a = Exists (v, a)

  let gen_relop = function
    | EQ -> Eq
    | NE -> Ne
    | GE -> Ge
    | LE -> Le
    | GT -> Gt
    | LT -> Lt

  let rec gen_value = function
    | UNARY (MINUS, e) -> VUop (Neg, gen_value e)
    | UNARY (NOT, e) -> failwith "'!' in logical expression"
    | BINARY (ADD, e1, e2) -> VBinop (Add, gen_value e1, gen_value e2)
    | BINARY (SUB, e1, e2) -> VBinop (Sub, gen_value e1, gen_value e2)
    | BINARY (MUL, e1, e2) -> VBinop (Mul, gen_value e1, gen_value e2)
    | BINARY (DIV, e1, e2) -> VBinop (Div, gen_value e1, gen_value e2)
    | BINARY (MOD, e1, e2) -> VBinop (Mod, gen_value e1, gen_value e2)
    | BINARY (CONS, e1, e2) -> VBinop (Cons, gen_value e1, gen_value e2)
    | BINARY (APPEND, e1, e2) -> VBinop (Append, gen_value e1, gen_value e2)
    | BINARY (SEPIMP, e1, e2) -> failwith "'-*' in logical expression"
    | BINARY (AND, e1, e2) -> failwith "'&&' in logical expression"
    | FUNCAPP (f, args) -> VFApp (f, List.map gen_value args)
    | CONSTANT n -> VLiteral (LInt n)
    | VARIABLE v -> VVar (FreeV v)
    | TUPLE args -> VTuple (List.map gen_value args)
    | RELATION _ -> failwith "relation operator in logical expression"
    | FORALL _ -> failwith "'forall' in logical expression"
    | EXISTS _ -> failwith "'exists' in logical expression"

  let rec gen_assertion = function
    | UNARY (NOT, e) -> Not (gen_assertion e)
    | UNARY (MINUS, _) -> failwith "'-' as assertion"
    | BINARY (ADD, _, _) -> failwith "'+' as assertion"
    | BINARY (SUB, _, _) -> failwith "'-' as assertion"
    | BINARY (MUL, e1, e2) -> SepConj (gen_assertion e1, gen_assertion e2)
    | BINARY (DIV, _, _) -> failwith "'/' as assertion"
    | BINARY (MOD, _, _) -> failwith "'%' as assertion"
    | BINARY (CONS, _, _) -> failwith "'::' as assertion"
    | BINARY (APPEND, _, _) -> failwith "'++' as assertion"
    | BINARY (SEPIMP, e1, e2) -> SepImpl (gen_assertion e1, gen_assertion e2)
    | BINARY (AND, e1, e2) -> And (gen_assertion e1, gen_assertion e2)
    | FUNCAPP (f, args) -> Predicate (f, List.map gen_value args)
    | CONSTANT _ -> failwith "constant as assertion"
    | VARIABLE p -> Proposition p
    | FORALL (vars, a) ->
        List.fold_right forall
          (List.map (fun n -> FreeV n) vars)
          (gen_assertion a)
    | EXISTS (vars, a) ->
        List.fold_right exists
          (List.map (fun n -> FreeV n) vars)
          (gen_assertion a)
    | RELATION (op, e1, e2) ->
        Relation (gen_relop op, gen_value e1, gen_value e2)
    | TUPLE _ -> failwith "tuple as assertion"
end

let rec convert_var_val f = function
  | VLiteral lit -> VLiteral lit
  | VVar v -> VVar (f v)
  | VBinop (op, v1, v2) ->
      VBinop (op, convert_var_val f v1, convert_var_val f v2)
  | VUop (op, v) -> VUop (op, convert_var_val f v)
  | VTuple eles -> VTuple (List.map (convert_var_val f) eles)
  | VFApp (fn, vl) -> VFApp (fn, List.map (convert_var_val f) vl)

(* logically unreachable, for debugging *)
exception Unreachable

(* rename : rename all free variables *)
let rename_v n i =
  let rv = function
    | FreeV n' -> if n = n' then BoundV (n, i) else FreeV n'
    | v -> v
  in
  convert_var_val rv

let rec rename_a n i a =
  match a with
  | Proposition _ -> a
  | Relation (rel, v1, v2) -> Relation (rel, rename_v n i v1, rename_v n i v2)
  | Predicate (p, vl) -> Predicate (p, List.map (rename_v n i) vl)
  | And (a1, a2) -> And (rename_a n i a1, rename_a n i a2)
  | Not a -> Not (rename_a n i a)
  | SepConj (a1, a2) -> SepConj (rename_a n i a1, rename_a n i a2)
  | SepImpl (a1, a2) -> SepImpl (rename_a n i a1, rename_a n i a2)
  | Forall (FreeV n', a) ->
      (* name shadow *)
      let new_a = if n = n' then a else rename_a n i a in
      Forall (FreeV n', new_a)
  | Exists (FreeV n', a) ->
      let new_a = if n = n' then a else rename_a n i a in
      Exists (FreeV n', new_a)
  | Forall (v, a) -> Forall (v, rename_a n i a)
  | Exists (v, a) -> Exists (v, rename_a n i a)

let rec exists_lift_list l a =
  match a with
  | Proposition _ -> (l, a)
  | Relation _ -> (l, a)
  | Predicate _ -> (l, a)
  | And (a1, a2) ->
      let l1, a1 = exists_lift_list l a1 in
      let l2, a2 = exists_lift_list l1 a2 in
      (l2, And (a1, a2))
  | Not a ->
      let l1, a1 = exists_lift_list l a in
      (l1, Not a1)
  | SepConj (a1, a2) ->
      let l1, a1 = exists_lift_list l a1 in
      let l2, a2 = exists_lift_list l1 a2 in
      (l2, SepConj (a1, a2))
  | SepImpl (a1, a2) ->
      let l1, a1 = exists_lift_list l a1 in
      let l2, a2 = exists_lift_list l1 a2 in
      (l2, SepImpl (a1, a2))
  | Exists (v, a) -> exists_lift_list (v :: l) a
  | Forall (v, a) -> (l, Forall (v, a))

let exists_lift a =
  let vars, a = exists_lift_list [] a in
  (List.rev vars, a)

module Show : sig
  val string_of_assertion : assertion -> string
end = struct
  let show_var = function
    | FreeV n -> "#" ^ n
    | BoundV (n, i) -> n ^ string_of_int i

  let show_binop = function
    | Add -> " + "
    | Sub -> " - "
    | Mul -> " * "
    | Div -> " / "
    | Mod -> " % "
    | Cons -> " :: "
    | Append -> " ++ "

  let show_uop = function Neg -> "-"

  let show_rel = function
    | Eq -> " == "
    | Ne -> " != "
    | Lt -> " < "
    | Le -> " <= "
    | Gt -> " > "
    | Ge -> " >= "

  let rec show_value v =
    match v with
    | VLiteral (LInt n) -> string_of_int n
    | VVar v -> show_var v
    | VBinop (op, v1, v2) ->
        "(" ^ show_value v1 ^ show_binop op ^ show_value v2 ^ ")"
    | VUop (op, v) -> "(" ^ show_uop op ^ show_value v ^ ")"
    | VTuple eles -> "{" ^ show_params eles ^ "}"
    | VFApp (n, ps) -> n ^ "(" ^ show_params ps ^ ")"

  and show_params ps =
    match ps with
    | [] -> ""
    | [ p ] -> show_value p
    | p :: ps -> show_value p ^ ", " ^ show_params ps

  let rec show_assertion = function
    | Forall (v, a) -> "forall " ^ show_var v ^ ", " ^ show_assertion a
    | Exists (v, a) -> "exists " ^ show_var v ^ ", " ^ show_assertion a
    | Proposition p -> p
    | And (a1, a2) -> show_assertion a1 ^ " && " ^ show_assertion a2
    | Not a -> "! " ^ show_assertion a
    | SepConj (a1, a2) -> show_assertion a1 ^ " * " ^ show_assertion a2
    | SepImpl (a1, a2) -> show_assertion a1 ^ " -* " ^ show_assertion a2
    | Relation (rel, v1, v2) -> show_value v1 ^ show_rel rel ^ show_value v2
    | Predicate (pred, vs) -> pred ^ "(" ^ show_params vs ^ ")"

  let rec sepc_to_list = function
    | SepConj (a1, a2) -> List.append (sepc_to_list a1) (sepc_to_list a2)
    | a -> [ a ]

  let rec extr_exists = function
    | Exists (v, a) ->
        let vs, a' = extr_exists a in
        (v :: vs, a')
    | a -> ([], a)

  let sep_params to_string sep = function
    | [] -> ""
    | [ a ] -> to_string a
    | h :: t ->
        List.fold_left (fun s x -> s ^ sep ^ to_string x) (to_string h) t

  let string_of_assertion a =
    let ex_vars, a = extr_exists a in
    let alist = sepc_to_list a in
    let ex_str =
      match ex_vars with
      | [] -> ""
      | _ :: _ -> "exists " ^ sep_params show_var " " ex_vars ^ ", "
    in
    let a_str =
      sep_params (fun a -> "(" ^ show_assertion a ^ ")") " * " alist
    in
    ex_str ^ a_str
end

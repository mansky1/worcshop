From Coq Require Lists.List.
From compcert Require Import Coqlib AST Clight SimplExpr Cop Memory.
From compcert Require Import AClight PLSDef.

Section PARSER.

Variable avar: Type.         (* variable in assertion *)
Variable a: Type.            (* assertion *)
Variable ex: avar -> a -> a. (* exists v, a *)

Function makeif (cond: expr) (s1 s2: C_statement avar a) :=
  match eval_simpl_expr cond with
  | Some v =>
      match bool_val v (typeof cond) Mem.empty with
      | Some b => if b then s1 else s2
      | None   => Cifthenelse cond s1 s2
      end
  | None => Cifthenelse cond s1 s2
  end.

Fixpoint fold_exgiven (base : a) (givens : list avar) (stmt : C_statement avar a) : C_statement avar a :=
  match givens with
  | nil => stmt
  | gid :: rest => Cexgiven gid (List.fold_right ex base rest) (fold_exgiven base rest stmt)
  end.

Definition while_to_loop (cond: expr) (body: C_statement avar a) :=
  Cloop (Csequence (makeif cond Cskip Cbreak) body) Cskip.

Definition inv_while_to_loop (inv: a) (cond: expr) (body: C_statement avar a) :=
  Cloop (Csequence (Cassert inv) (Csequence (makeif cond Cskip Cbreak) body)) Cskip.

Fixpoint to_cstatement_simple (ps: pstmt_a avar a) : option (C_statement avar a) :=
  match ps with
  | PSskip => Some Cskip
  | PSassign lhs rhs => Some (Cassign lhs rhs)
  | PScall ret f args => Some (Ccall ret f args)
  | PSset lhs rhs => Some (Cset lhs rhs)
  | PSsequence ps1 ps2 =>
    match to_cstatement_simple ps1 with
    | None => None
    | Some s1 =>
        match to_cstatement_simple ps2 with
        | None => None
        | Some s2 => Some (Csequence s1 s2)
        end
    end
  | _ => None
  end.

Fixpoint parse_cstatement_base (src: list (pstmt_a avar a)) (fuel: nat) : option (C_statement avar a * list (pstmt_a avar a)) :=
  match fuel with
  | O => None
  | S fuel =>
    match src with
    | nil => None
    | ps :: rest =>
        match ps with
        | PSskip => Some (Cskip, rest)
        | PSbreak => Some (Cbreak, rest)
        | PScontinue => Some (Ccontinue, rest)
        | PSreturn ret => Some (Creturn ret, rest)
        | PSassign lhs rhs => Some (Cassign lhs rhs, rest)
        | PScall None f args => Some (Ccall None f args, rest)
        | PScall ret f args =>
            match rest with
            | PSset lhs rhs :: rest =>
                Some (Csequence (Ccall ret f args) (Cset lhs rhs), rest)
            | _ => Some (Ccall ret f args, rest)
            end
        | PSset lhs rhs => Some (Cset lhs rhs, rest)
        | PSif cond =>
            match parse_cstatement_base rest fuel with
            | Some (t, PSelse :: rest) =>
                match parse_cstatement_base rest fuel with
                | Some (f, rest) => Some (makeif cond t f, rest)
                | _ => None
                end
            | Some (t, rest) => Some (makeif cond t Cskip, rest)
            | _ => None
            end
        | PSwhile cond =>
            match parse_cstatement_base rest fuel with
            | None => None
            | Some (body, rest) => Some (while_to_loop cond body, rest)
            end
        | PSfor opt_init opt_cond opt_incr =>
            match parse_cstatement_base rest fuel with
            | None => None
            | Some (body, rest) =>
                let body :=
                  match opt_cond with
                  | None => body
                  | Some cond => Csequence (makeif cond Cskip Cbreak) body
                  end in
                let opt_incr :=
                  match opt_incr with
                  | None => Some Cskip
                  | Some incr => to_cstatement_simple incr
                  end in
                match opt_incr with
                | None => None
                | Some incr =>
                    match opt_init with
                    | None => Some (Cloop body incr, rest)
                    | Some init =>
                        match to_cstatement_simple init with
                        | None => None
                        | Some init => Some (Csequence init (Cloop body incr), rest)
                        end
                    end
                end
            end
        | PSassert (Assertion a) => Some (Cassert a, rest)
        | PSassert (Invariant inv) =>
            match rest with
            | PSwhile cond :: rest =>
                match parse_cstatement_base rest fuel with
                | None => None
                | Some (body, rest) => Some (inv_while_to_loop inv cond body, rest)
                end
            | PSfor opt_init opt_cond opt_incr :: rest =>
                match parse_cstatement_base rest fuel with
                | None => None
                | Some (body, rest) =>
                    let body :=
                      match opt_cond with
                      | None => body
                      | Some cond => Csequence (Cassert inv) (Csequence (makeif cond Cskip Cbreak) body)
                      end in
                    let opt_incr :=
                      match opt_incr with
                      | None => Some Cskip
                      | Some incr => to_cstatement_simple incr
                      end in
                    match opt_incr with
                    | None => None
                    | Some incr =>
                        match opt_init with
                        | None => Some (Cloop body incr, rest)
                        | Some init =>
                            match to_cstatement_simple init with
                            | None => None
                            | Some init => Some (Csequence init (Cloop body incr), rest)
                            end
                        end
                    end
                end
            | _ => None
            end
        | PSassert (Assertion_exgiven base givens) =>
            match parse_cstatement rest fuel with
            | None => None
            | Some (stmt, rest) => Some (fold_exgiven base givens stmt, rest)
            end
        | PSlbrace =>
            match parse_cstatement rest fuel with
            | Some (stmt, PSrbrace :: rest) => Some (stmt, rest)
            | _ => None
            end
        | _ => None
        end
    end
  end
with parse_cstatement (src: list (pstmt_a avar a)) (fuel: nat) : option (C_statement avar a * list (pstmt_a avar a)) :=
  match fuel with
  | O => None
  | S fuel =>
    match parse_cstatement_base src fuel with
    | None => None
    | Some (stmt1, rest) =>
        match parse_cstatement rest fuel with
        | None => Some (stmt1, rest)
        | Some (stmt2, rest) => Some (Csequence stmt1 stmt2, rest)
        end
    end
  end.

Definition parse_cfunction (src: list (pstmt_a avar a)) (fuel: nat) : option (C_function avar a * list (pstmt_a avar a)) :=
  match src with
  | PSlbrace :: PSassert (Funcspec withs pre post) :: rest =>
      match parse_cstatement rest fuel with
      | Some (body, PSrbrace :: rest) => Some (Cfunc withs pre post body, rest)
      | _ => None
      end
  | _ => None
  end.

Definition concat_pstmts (src: list (pstmt_a avar a)) : option (C_function avar a) :=
  let fuel := Nat.mul 2 (length src) in
  match parse_cfunction src fuel with
  | Some (f, nil) => Some f
  | _ => None
  end.

End PARSER.
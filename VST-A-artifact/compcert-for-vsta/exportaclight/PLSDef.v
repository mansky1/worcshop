From Coq Require Import String.
From compcert Require Import Coqlib AST.
From compcert Require Ctypes.
From compcert Require Import ExprvalDef.

Inductive proposition : Type :=
  | TT : proposition
  | FF : proposition
  | Pnot : proposition -> proposition (**r ! a *)
  | Pand : proposition -> proposition -> proposition (**r a && b *)
  | Pvle : expr_val -> expr_val -> proposition  (**r a <= b *)
  | Pvge : expr_val -> expr_val -> proposition  (**r a >= b *)
  | Pvlt : expr_val -> expr_val -> proposition  (**r a < b *)
  | Pvgt : expr_val -> expr_val -> proposition  (**r a > b *)
  | Pveq : expr_val -> expr_val -> proposition  (**r a = b *)
  | Pforall : ident -> proposition -> proposition (**r forall x, p *)
  | Pexists : ident -> proposition -> proposition (**r exists x, p *)
  | Ppred : string -> list expr_val -> proposition (**r f(a, b, ...) *)
.

Inductive local : Type :=
  | Temp : ident -> expr_val -> local
.

Inductive separation : Type :=
  | Emp : separation
  | Data_at : Ctypes.type -> expr_val -> expr_val -> separation (* Tsh *)
  | Spred : string -> list expr_val -> separation
  | Wand : separation -> separation -> separation
.

Inductive assertion : Type :=
  | Anormal : list proposition -> list local -> list separation -> assertion
  | Aex : ident -> assertion -> assertion
.
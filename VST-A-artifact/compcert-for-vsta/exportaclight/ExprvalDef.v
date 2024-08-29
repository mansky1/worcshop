From Coq Require Import String.
From compcert Require Import Coqlib AST.
From compcert Require Ctypes.

Inductive unary_operation : Type :=
  | Oneg : unary_operation              (**r opposite (unary [-]) *)
.

Inductive binary_operation : Type :=
  | Oadd : binary_operation             (**r addition (binary [+]) *)
  | Osub : binary_operation             (**r subtraction (binary [-]) *)
  | Omul : binary_operation             (**r multiplication (binary [*]) *)
  | Odiv : binary_operation             (**r division ([/]) *)
  | Omod : binary_operation             (**r remainder ([%]) *)
  | Ocons : binary_operation            (**r list cons ([::]) *)
  | Oapp : binary_operation             (**r list append ([++]) *)
.

Inductive expr_val : Type :=
  | Vunit : expr_val
  | Vint : Z -> expr_val
  | Vvar : ident -> expr_val                     (** logical variable *)
  | Vuop : unary_operation -> expr_val -> expr_val (** unary operation *)
  | Vbop : binary_operation -> expr_val -> expr_val -> expr_val (** binary operation *)
  | Vpair : expr_val -> expr_val -> expr_val
  | Vfield_addr : expr_val -> Ctypes.type -> ident -> expr_val (** field_address v type field *)
  | Vfapp : string -> list expr_val -> expr_val
.
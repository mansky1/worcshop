From Coq Require Import Lists.List.
From compcert Require Import Clight AST.
Import List.ListNotations.
Local Open Scope list.

Inductive C_statement {avar: Type} {a: Type} : Type :=
  | Cassert : a -> C_statement
  | Cexgiven : avar -> a -> C_statement -> C_statement
  | Cskip : C_statement
  | Csequence : C_statement -> C_statement -> C_statement
  | Cassign : expr -> expr -> C_statement
  | Ccall : option ident -> expr -> list expr -> C_statement
  | Cset : ident -> expr -> C_statement
  | Cifthenelse : expr -> C_statement -> C_statement -> C_statement
  | Cloop : C_statement -> C_statement -> C_statement
  | Cbreak : C_statement
  | Ccontinue : C_statement
  | Creturn : option expr -> C_statement
.

Arguments C_statement: clear implicits.

Inductive C_function {avar: Type} {a: Type} : Type :=
  | Cfunc : list avar -> a -> a -> C_statement avar a -> C_function
.

Arguments C_function: clear implicits.

Inductive user_assertion {avar: Type} {a: Type} : Type :=
  | Funcspec : list avar -> a -> a -> user_assertion
  | Assertion : a -> user_assertion
  | Assertion_exgiven : a -> list avar -> user_assertion
  | Invariant : a -> user_assertion
.

Arguments user_assertion: clear implicits.

Definition pstmt_a avar a := partial_statement_with (user_assertion avar a).

(********* The below is deeply embedded split ********)

Definition is_nil {A: Type} (l: list A) :=
  match l with
  | nil => true
  | _ => false
  end.

Section Split.

Context {avar: Type} {a: Type}.

Variable exp: avar -> a -> a.

Variable FF: a.

Inductive atom_statement : Type :=
| Askip : atom_statement                   (**r do nothing *)
| Aassign : expr -> expr -> atom_statement (**r assignment [lvalue = rvalue] *)
| Aset : ident -> expr -> atom_statement   (**r assignment [tempvar = rvalue] *)
| Acall: option ident -> expr 
          -> list expr -> atom_statement   (**r function call *).

Definition path:= list (bool * expr + atom_statement) .

Inductive atom : Type :=
| mk_atom : path -> atom.

Notation atoms := (list atom). 

Inductive atom_ret : Type :=
| mk_atom_ret : path -> option expr -> atom_ret.

Notation atom_rets := (list atom_ret).

Inductive full_path : Type :=
| mk_full_path : a -> path -> a -> full_path
| bind_full_path : avar -> full_path -> full_path.

Notation full_paths := (list full_path).

Inductive full_ret_path : Type :=
| mk_full_ret_path : a -> path -> option expr -> a -> full_ret_path
| bind_full_ret_path : avar -> full_ret_path -> full_ret_path.

Notation full_ret_paths := (list full_ret_path).

Inductive partial_pre : Type :=
| mk_partial_pre : path -> a -> partial_pre.

Notation partial_pres := (list partial_pre).

Inductive partial_post : Type :=
| mk_partial_post : a -> path -> partial_post.

Notation partial_posts := (list partial_post).

Inductive partial_post_ret : Type :=
| mk_partial_post_ret : a -> path -> option expr -> partial_post_ret.

Notation partial_post_rets := (list partial_post_ret).

Record result_rec := mk_result_rec {
  res_pre : partial_pres;
  res_path : full_paths;
  res_post_normal : partial_posts;
  res_post_break : partial_posts;
  res_post_continue : partial_posts;
  res_post_return : partial_post_rets;
  res_atom_normal : atoms;
  res_atom_break : atoms;
  res_atom_continue : atoms;
  res_atom_return : atom_rets;
}.

Definition result := option result_rec.

Definition atom_conn_return atom1 atom2 :=
  match atom1, atom2 with
  | mk_atom path1, mk_atom_ret path2 retval =>
      mk_atom_ret (path1 ++ path2) retval
  end.

Definition atom_conn_returns atom1 atoms2 :=
  map (atom_conn_return atom1) atoms2.

Definition atoms_conn_returns atoms1 atoms2 :=
  concat (map (fun atom1 => atom_conn_returns atom1 atoms2) atoms1).

Definition atom_conn_atom atom1 atom2 :=
  match atom1, atom2 with
  | mk_atom path1, mk_atom path2 =>
      mk_atom (path1 ++ path2)
  end.

Definition atom_conn_atoms atom1 atoms2 :=
  map (atom_conn_atom atom1) atoms2.

Definition atoms_conn_atoms atoms1 atoms2 :=
  concat (map (fun atom1 => atom_conn_atoms atom1 atoms2) atoms1).

Definition atom_conn_pre atom1 pre2 :=
  match atom1, pre2 with
  | mk_atom path1, mk_partial_pre path2 P =>
      mk_partial_pre (path1 ++ path2) P
  end.

Definition atom_conn_pres atom1 pres2 :=
  map (atom_conn_pre atom1) pres2.

Fixpoint atoms_conn_pres atoms1 pres2 :=
  match atoms1 with
  | [] => []
  | atom1 :: atoms1' =>
    atom_conn_pres atom1 pres2 ++ atoms_conn_pres atoms1' pres2
  end.

Definition post_conn_atom post1 atom2 :=
  match post1, atom2 with
  | mk_partial_post P path1, mk_atom path2 =>
      mk_partial_post P (path1 ++ path2)
  end.

Definition posts_conn_atom posts1 atom2 :=
  map (fun post1 => post_conn_atom post1 atom2) posts1.

Definition post_conn_return post1 atom2 :=
  match post1, atom2 with
  | mk_partial_post P path1, mk_atom_ret path2 retval =>
      mk_partial_post_ret P (path1 ++ path2) retval
  end.
  
Definition posts_conn_return posts1 atom2 :=
  map (fun post1 => post_conn_return post1 atom2) posts1.

Fixpoint posts_conn_atoms posts1 atoms2 :=
  match atoms2 with
  | [] => []
  | atom2 :: atoms2' =>
    posts_conn_atom posts1 atom2 ++ posts_conn_atoms posts1 atoms2'
  end.

Fixpoint posts_conn_returns posts1 atoms2 :=
  match atoms2 with
  | [] => []
  | atom2 :: atoms2' =>
    posts_conn_return posts1 atom2 ++ posts_conn_returns posts1 atoms2'
  end.

Definition post_conn_pre (post1: partial_post) (pre2: partial_pre): full_path :=
  match post1, pre2  with
  | mk_partial_post P path1, mk_partial_pre path2 Q =>
    mk_full_path P (path1 ++ path2) Q
  end.

Definition post_conn_pres post1 pres2 :=
  map (post_conn_pre post1) pres2.

Fixpoint posts_conn_pres (posts1: partial_posts) (pres2: partial_pres) : full_paths :=
  match posts1 with
  | [] => []
  | post1 :: posts1' =>
    post_conn_pres post1 pres2 ++ posts_conn_pres posts1' pres2
  end.

Definition add_exp_to_pre b e (pre : partial_pre ) :=
  match pre with
  | mk_partial_pre path Q =>
      mk_partial_pre ((inl (b, e))::path) Q
  end.

Definition add_exp_to_pres b e pres :=
  map (add_exp_to_pre b e) pres.

Definition add_exp_to_atom b e (atom: atom) :=
  match atom with
  | mk_atom path =>
     mk_atom ((inl (b, e))::path)
  end.

Definition add_exp_to_atoms b e atoms :=
  map (add_exp_to_atom b e) atoms.

Definition add_exp_to_ret_atom b e (atom: atom_ret) :=
  match atom with
  | mk_atom_ret path retval =>
      mk_atom_ret ((inl (b, e))::path) retval
  end.

Definition add_exp_to_ret_atoms b e atoms :=
  map (add_exp_to_ret_atom b e) atoms.

Definition add_P_to_pre P pre :=
  match pre with
  | mk_partial_pre path Q =>
      mk_full_path P path Q
  end.

Definition add_P_to_pres P := map (add_P_to_pre P).

Definition add_P_to_atom P atom :=
  match atom with
  | mk_atom path =>
      mk_partial_post P path
  end.

Definition add_P_to_atoms P := map (add_P_to_atom P).

Definition add_P_to_atom_ret P atom :=
  match atom with
  | mk_atom_ret path retval =>
      mk_partial_post_ret P path retval
  end.

Definition add_P_to_atom_rets P := map (add_P_to_atom_ret P).

Definition add_Q_to_post post Q :=
  match post with
  | mk_partial_post P path =>
      mk_full_path P path Q
  end.

Definition add_Q_to_posts posts Q := map (fun post => add_Q_to_post post Q) posts.

Definition add_Q_to_post_ret post Q :=
  match post with
  | mk_partial_post_ret P path optval =>
      mk_full_ret_path P path optval Q
  end.

Definition add_Q_to_post_rets posts Q :=
  map (fun post => add_Q_to_post_ret post Q) posts.

Definition add_Q_to_atom atom Q :=
  match atom with
  | mk_atom path =>
      mk_partial_pre path Q
  end.

Definition add_Q_to_atoms atoms Q := map (fun atom => add_Q_to_atom atom Q) atoms.

Definition bind_full_paths x := map (bind_full_path x).

Definition bind_full_ret_paths x := map (bind_full_ret_path x).

Definition nested_bind_full_paths xs paths :=
  fold_right bind_full_paths paths xs.

Definition nested_bind_full_ret_paths xs paths :=
  fold_right bind_full_ret_paths paths xs.

Definition flatten_partial_post_binds
             (x: avar) (post: partial_post): partial_post :=
  match post with
  | mk_partial_post P path =>
      mk_partial_post (exp x P) path
  end.

Definition flatten_partial_posts_binds
             (x: avar) (posts: partial_posts): partial_posts :=
  map (flatten_partial_post_binds x) posts.

Definition flatten_partial_post_ret_binds
             (x: avar) (post: partial_post_ret): partial_post_ret :=
  match post with
  | mk_partial_post_ret P path retval =>
      mk_partial_post_ret (exp x P) path retval
  end.

Definition flatten_partial_post_rets_binds
             (x: avar) (posts: partial_post_rets): partial_post_rets :=
  map (flatten_partial_post_ret_binds x) posts.

Definition split_assert (P: a) : result :=
  Some ( mk_result_rec
  (* res_pre *)           [ mk_partial_pre nil P ]
  (* res_path *)          []
  (* res_post_normal *)   [ mk_partial_post P nil]
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   []
  (* res_atom_break *)    []
  (* res_atom_continue *) []
  (* res_atom_return *)   [])
.

Definition split_sequence (res1 res2: result): result :=
match res1, res2 with
| None, _ => None
| _, None => None
| Some (mk_result_rec
          pre1 path1 
          post_normal1 post_break1
          post_continue1 post_return1
          atom_normal1 atom_break1
          atom_continue1 atom_return1),
  Some (mk_result_rec
          pre2 path2
          post_normal2 post_break2
          post_continue2 post_return2
          atom_normal2 atom_break2
          atom_continue2 atom_return2) =>
  Some
    (mk_result_rec
      (* res_pre *)
      (pre1 ++ atoms_conn_pres atom_normal1 pre2)
      (* res_path *)
      (path1 ++ path2 ++ posts_conn_pres post_normal1 pre2)
      (* res_post_normal *)
      (post_normal2 ++ posts_conn_atoms post_normal1 atom_normal2)
      (* res_post_break *)
      (post_break1 ++ post_break2 ++ posts_conn_atoms post_normal1 atom_break2)
      (* res_post_continue *)
      (post_continue1 ++ post_continue2 ++ posts_conn_atoms post_normal1 atom_continue2)
      (* res_post_return *)
      (post_return1 ++ post_return2 ++ posts_conn_returns post_normal1 atom_return2)
      (* res_atom_normal *)
      (atoms_conn_atoms atom_normal1 atom_normal2)
      (* res_atom_break *)
      (atom_break1 ++ atoms_conn_atoms atom_normal1 atom_break2)
      (* res_atom_continue *)
      (atom_continue1 ++ atoms_conn_atoms atom_normal1 atom_continue2)
      (* res_atom_return *)
      (atom_return1 ++ atoms_conn_returns atom_normal1 atom_return2))
end.

Definition split_exgiven (x: avar) (P: a) (res: result): result :=
match res with
| None => None    
| Some (mk_result_rec pre path post_normal post_break post_continue post_return atom_normal atom_break atom_continue atom_return) =>
    let xP := exp x P in
      Some
        (mk_result_rec
          (* res_pre *)
          ( [ mk_partial_pre nil xP ] )
          (* res_path *)
          ( bind_full_paths x (path ++ add_P_to_pres P pre) )
          (* res_post_normal *)
          ( flatten_partial_posts_binds x post_normal ++ add_P_to_atoms xP atom_normal )
          (* res_post_break *)
          ( flatten_partial_posts_binds x post_break ++ add_P_to_atoms xP atom_break )
          (* res_post_continue *)
          ( flatten_partial_posts_binds x post_continue ++ add_P_to_atoms xP atom_continue )
          (* res_post_return *)
          ( flatten_partial_post_rets_binds x post_return ++ add_P_to_atom_rets xP atom_return)
          (* res_atom_normal *)
          []
          (* res_atom_break *)
          []
          (* res_atom_continue *)
          []
          (* res_atom_return *)
          [])
end.

Definition split_skip : result :=
  Some (mk_result_rec
  (* res_pre *)           []
  (* res_path *)          []
  (* res_post_normal *)   []
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   [ mk_atom nil ]
  (* res_atom_break *)    []
  (* res_atom_continue *) []
  (* res_atom_return *)   [])
.

Definition split_assign e1 e2 : result :=
  Some (mk_result_rec
  (* res_pre *)           []
  (* res_path *)          []
  (* res_post_normal *)   []
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   [ mk_atom [inr (Aassign e1 e2)] ]
  (* res_atom_break *)    []
  (* res_atom_continue *) []
  (* res_atom_return *)   [])
  .

Definition split_call id e args : result :=
  Some (mk_result_rec
  (* res_pre *)           []
  (* res_path *)          []
  (* res_post_normal *)   []
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   [ mk_atom [inr (Acall id e args)] ]
  (* res_atom_break *)    []
  (* res_atom_continue *) []
  (* res_atom_return *)   [])
  .

Definition split_set e1 e2 : result :=
  Some (mk_result_rec
  (* res_pre *)           []
  (* res_path *)          []
  (* res_post_normal *)   []
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   [ mk_atom [inr (Aset e1 e2)] ]
  (* res_atom_break *)    []
  (* res_atom_continue *) []
  (* res_atom_return *)   [])
  .

Definition split_break : result :=
  Some (mk_result_rec
  (* res_pre *)           []
  (* res_path *)          []
  (* res_post_normal *)   []
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   []
  (* res_atom_break *)    [ mk_atom nil ]
  (* res_atom_continue *) []
  (* res_atom_return *)   [])
  .

Definition split_continue : result :=
  Some (mk_result_rec
  (* res_pre *)           []
  (* res_path *)          []
  (* res_post_normal *)   []
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   []
  (* res_atom_break *)    []
  (* res_atom_continue *) [ mk_atom nil]
  (* res_atom_return *)   [])
  .

Definition split_return e : result :=
  Some (mk_result_rec
  (* res_pre *)           []
  (* res_path *)          []
  (* res_post_normal *)   []
  (* res_post_break *)    []
  (* res_post_continue *) []
  (* res_post_return *)   []
  (* res_atom_normal *)   []
  (* res_atom_break *)    []
  (* res_atom_continue *) []
  (* res_atom_return *)   [ mk_atom_ret nil e ])
  .

Definition split_ifthenelse (e: expr) res1 res2 := 
match res1, res2 with
| None, _ => None
| _, None => None
| Some (mk_result_rec
          pre1 path1 
          post_normal1 post_break1
          post_continue1 post_return1
          atom_normal1 atom_break1
          atom_continue1 atom_return1),
  Some (mk_result_rec
          pre2 path2
          post_normal2 post_break2
          post_continue2 post_return2
          atom_normal2 atom_break2
          atom_continue2 atom_return2) =>
  Some
    (mk_result_rec
      (* res_pre *)
      (add_exp_to_pres true e pre1 ++ add_exp_to_pres false e pre2)
      (* res_path *)
      (path1 ++ path2)
      (* res_post_normal *)
      (post_normal1 ++ post_normal2)
      (* res_post_break *)
      (post_break1 ++ post_break2)
      (* res_post_continue *)
      (post_continue1 ++ post_continue2)
      (* res_post_return *)
      (post_return1 ++ post_return2)
      (* res_atom_normal *)
      (add_exp_to_atoms true e atom_normal1 ++
       add_exp_to_atoms false e atom_normal2)
      (* res_atom_break *)
      (add_exp_to_atoms true e atom_break1 ++
       add_exp_to_atoms false e atom_break2)     
      (* res_atom_continue *)
      (add_exp_to_atoms true e atom_continue1 ++
       add_exp_to_atoms false e atom_continue2)
      (* res_atom_return *)
      (add_exp_to_ret_atoms true e atom_return1 ++
       add_exp_to_ret_atoms false e atom_return2))
end.

Definition split_loop res1 res2 := 
match res1, res2 with
| None, _ => None
| _, None => None
| Some (mk_result_rec
          pre1 path1 
          post_normal1 post_break1
          post_continue1 post_return1
          atom_normal1 atom_break1
          atom_continue1 atom_return1),
  Some (mk_result_rec
          pre2 path2
          post_normal2 post_break2
          post_continue2 post_return2
          atom_normal2 atom_break2
          atom_continue2 atom_return2) =>
  if orb (is_nil atom_normal2) (andb (is_nil atom_normal1) (is_nil atom_continue1))
  then
    Some
      (mk_result_rec
       (* res_pre *)
         (pre1 ++
          atoms_conn_pres atom_normal1 pre2 ++
          atoms_conn_pres atom_continue1 pre2 ++
          atoms_conn_pres atom_normal1
            (add_Q_to_atoms atom_continue2 FF) ++
          atoms_conn_pres atom_continue1
            (add_Q_to_atoms atom_continue2 FF))
       (* res_path *)
         (path1 ++ path2 ++ 
          posts_conn_pres post_normal1 pre2 ++
          posts_conn_pres post_continue1 pre2 ++
          posts_conn_pres post_normal2 pre1 ++
          posts_conn_pres post_normal1
            (atoms_conn_pres atom_normal2 pre1) ++
          posts_conn_pres post_continue1
            (atoms_conn_pres atom_normal2 pre1) ++
          posts_conn_pres 
            (posts_conn_atoms post_normal2 atom_normal1) pre2 ++
          posts_conn_pres 
            (posts_conn_atoms post_normal2 atom_continue1) pre2 ++
          posts_conn_pres
            (posts_conn_atoms post_normal2 atom_normal1)
            (add_Q_to_atoms atom_continue2 FF) ++
          posts_conn_pres
            (posts_conn_atoms post_normal2 atom_continue1)
            (add_Q_to_atoms atom_continue2 FF) ++
          posts_conn_pres post_normal1
            (add_Q_to_atoms atom_continue2 FF) ++
          posts_conn_pres post_continue1
            (add_Q_to_atoms atom_continue2 FF) ++
          add_Q_to_posts post_continue2 FF)
      (* res_post_normal *)
         (post_break1 ++ post_break2 ++ 
          posts_conn_atoms post_normal1 atom_break2 ++
          posts_conn_atoms post_normal2 atom_break1 ++
          posts_conn_atoms post_continue1 atom_break2 ++
          posts_conn_atoms
            (posts_conn_atoms post_normal2 atom_normal1) atom_break2 ++
          posts_conn_atoms 
            (posts_conn_atoms post_normal2 atom_continue1) atom_break2 ++
          posts_conn_atoms post_normal1
            (atoms_conn_atoms atom_normal2 atom_break1) ++
          posts_conn_atoms post_continue1
            (atoms_conn_atoms atom_normal2 atom_break1))
      (* res_post_break *)    []
      (* res_post_continue *) []
      (* res_post_return *)
         (post_return1 ++ post_return2 ++ 
          posts_conn_returns post_normal1 atom_return2 ++
          posts_conn_returns post_continue1 atom_return2 ++
          posts_conn_returns post_normal2 atom_return1 ++
          posts_conn_returns 
            (posts_conn_atoms post_normal2 atom_normal1) atom_return2 ++
          posts_conn_returns 
            (posts_conn_atoms post_normal2 atom_continue1) atom_return2 ++
          posts_conn_returns post_normal1 
            (atoms_conn_returns atom_normal2 atom_return1) ++
          posts_conn_returns post_continue1 
            (atoms_conn_returns atom_normal2 atom_return1))
      (* res_atom_normal *)
        (atom_break1 ++
          atoms_conn_atoms atom_normal1 atom_break2 ++
          atoms_conn_atoms atom_continue1 atom_break2)
      (* res_atom_break *)    []
      (* res_atom_continue *) []
      (* res_atom_return *)
        (atom_return1 ++
          atoms_conn_returns atom_normal1 atom_return2 ++
          atoms_conn_returns atom_continue1 atom_return2 ))
  else None
end.

Fixpoint split_fun (s: C_statement avar a) : result :=
  match s with
  | Cassert P =>
      split_assert P
  | Cexgiven x P s =>
      split_exgiven x P (split_fun s)
  | Cskip => 
      split_skip
  | Csequence s1 s2 =>
      let res1 := split_fun s1 in
      let res2 := split_fun s2 in
      split_sequence res1 res2
  | Cassign e1 e2 =>
      split_assign e1 e2
  | Ccall id e args =>
      split_call id e args
  | Cset id e =>
      split_set id e
  | Cifthenelse e s1 s2 => 
      let res1 := split_fun s1 in
      let res2 := split_fun s2 in
      split_ifthenelse e res1 res2
  | Cloop s1 s2 => 
      let res1 := split_fun s1 in
      let res2 := split_fun s2 in
      split_loop res1 res2
  | Cbreak =>
      split_break
  | Ccontinue =>
      split_continue
  | Creturn e =>
      split_return e
  end.

Definition proof_goals (f: C_function avar a):
  option (full_paths * full_paths * full_ret_paths) :=
  match f with
  | Cfunc xs P Q s =>
      let res := split_fun s in
      match split_fun s with
      | Some (mk_result_rec
                pre path
                nil nil
                nil post_return
                nil nil
                nil atom_return) =>
        Some
          (nested_bind_full_paths xs (add_P_to_pres P pre ++ path),
           nil,
           nested_bind_full_ret_paths xs
             (add_Q_to_post_rets post_return Q ++
              add_Q_to_post_rets (add_P_to_atom_rets P atom_return) Q))
      | _ => None
      end
  end.

(* normal exit should be valid in void function *)
Definition proof_goals_void_return (f: C_function avar a):
  option (full_paths * full_paths * full_ret_paths) :=
  match f with
  | Cfunc xs P Q s =>
      let res := split_fun s in
      match split_fun s with
      | Some (mk_result_rec
                pre path
                post_normal nil
                nil         post_return
                atom_normal nil
                nil         atom_return) =>
        Some
          (nested_bind_full_paths xs (add_P_to_pres P pre ++ path),
           nested_bind_full_paths xs
             (add_Q_to_posts post_normal Q ++
              add_Q_to_posts (add_P_to_atoms P atom_normal) Q),
           nested_bind_full_ret_paths xs
             (add_Q_to_post_rets post_return Q ++
              add_Q_to_post_rets (add_P_to_atom_rets P atom_return) Q))
      | _ => None
      end
  end.

End Split.


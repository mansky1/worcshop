open Clight
open AClight

let dbg_pstmt = function
  | PSassert (Assertion a) -> "Assertion " ^ AAst.Show.string_of_assertion a
  | PSassert (Invariant a) -> "Invariant " ^ AAst.Show.string_of_assertion a
  | PSassert (Funcspec _) -> "Funcspec"
  | PSassert (Assertion_exgiven (a, givens)) ->
      AAst.Show.string_of_assertion a
      ^ " given "
      ^ List.fold_right ( ^ ) givens ""
  | PSskip -> "PSskip"
  | PSassign _ -> "PSassign"
  | PSset _ -> "PSset"
  | PScall _ -> "PScall"
  | PSbreak -> "PSbreak"
  | PScontinue -> "PScontinue"
  | PSreturn _ -> "PSreturn"
  | PSfor _ -> "PSfor"
  | PSwhile _ -> "PSwhile"
  | PSif _ -> "PSif"
  | PSelse -> "PSelse"
  | PSlbrace -> "PSlbrace"
  | PSrbrace -> "PSrbrace"
  | PSdecl _ -> "PSdecl"
  | PSbuiltin _ -> "PSbuiltin"
  | PSfake _ -> "PSfake"
  | PSsequence _ -> "PSsequence"

let dbg_pstmt' = function
  | PSassert _ -> "PSassert"
  | PSskip -> "PSskip"
  | PSassign _ -> "PSassign"
  | PSset _ -> "PSset"
  | PScall _ -> "PScall"
  | PSbreak -> "PSbreak"
  | PScontinue -> "PScontinue"
  | PSreturn _ -> "PSreturn"
  | PSfor _ -> "PSfor"
  | PSwhile _ -> "PSwhile"
  | PSif _ -> "PSif"
  | PSelse -> "PSelse"
  | PSlbrace -> "PSlbrace"
  | PSrbrace -> "PSrbrace"
  | PSdecl _ -> "PSdecl"
  | PSbuiltin _ -> "PSbuiltin"
  | PSfake _ -> "PSfake"
  | PSsequence _ -> "PSsequence"

let rec dbg_split_fun exp fF s =
  let result, name =
    match s with
    | Cassert p -> (split_assert p, "assert")
    | Cexgiven (x, p, s0) ->
        (split_exgiven exp x p (dbg_split_fun exp fF s0), "exgiven")
    | Cskip -> (split_skip, "skip")
    | Csequence (s1, s2) ->
        let res1 = dbg_split_fun exp fF s1 in
        let res2 = dbg_split_fun exp fF s2 in
        (split_sequence res1 res2, "seq")
    | Cassign (e1, e2) -> (split_assign e1 e2, "assign")
    | Ccall (id, e, args) -> (split_call id e args, "call")
    | Cset (id, e) -> (split_set id e, "set")
    | Cifthenelse (e, s1, s2) ->
        let res1 = dbg_split_fun exp fF s1 in
        let res2 = dbg_split_fun exp fF s2 in
        (split_ifthenelse e res1 res2, "ite")
    | Cloop (s1, s2) ->
        let res1 = dbg_split_fun exp fF s1 in
        let res2 = dbg_split_fun exp fF s2 in
        (split_loop fF res1 res2, "loop")
    | Cbreak -> (split_break, "break")
    | Ccontinue -> (split_continue, "continue")
    | Creturn e -> (split_return e, "return")
  in
  match result with
  | None ->
      print_string "fail ";
      print_endline name;
      result
  | Some res ->
      print_string "success ";
      print_endline name;
      result

let dbg_proof_goals exp fF = function
  | Cfunc (xs, p, q, s) -> (
      match dbg_split_fun exp fF s with
      | Some r -> (
          let {
            res_pre = pre;
            res_path = path0;
            res_post_normal = res_post_normal0;
            res_post_break = res_post_break0;
            res_post_continue = res_post_continue0;
            res_post_return = post_return;
            res_atom_normal = res_atom_normal0;
            res_atom_break = res_atom_break0;
            res_atom_continue = res_atom_continue0;
            res_atom_return = atom_return;
          } =
            r
          in
          match res_post_normal0 with
          | [] -> (
              match res_post_break0 with
              | [] -> (
                  match res_post_continue0 with
                  | [] -> (
                      match res_atom_normal0 with
                      | [] -> (
                          match res_atom_break0 with
                          | [] -> (
                              match res_atom_continue0 with
                              | [] ->
                                  Some
                                    ( nested_bind_full_paths xs
                                        (Datatypes.app (add_P_to_pres p pre)
                                           path0),
                                      nested_bind_full_ret_paths xs
                                        (Datatypes.app
                                           (add_Q_to_post_rets post_return q)
                                           (add_Q_to_post_rets
                                              (add_P_to_atom_rets p atom_return)
                                              q)) )
                              | _ :: _ ->
                                  print_endline "res_atom_continue <> []";
                                  None)
                          | _ :: _ ->
                              print_endline "res_atom_break <> []";
                              None)
                      | _ :: _ ->
                          print_endline "res_atom_normal <> []";
                          None)
                  | _ :: _ ->
                      print_endline "res_post_continue <> []";
                      None)
              | _ :: _ ->
                  print_endline "res_post_break <> []";
                  None)
          | _ :: _ ->
              print_endline "res_post_normal <> []";
              None)
      | None -> None)

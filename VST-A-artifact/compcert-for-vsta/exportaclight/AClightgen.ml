open AClightLib
open AClightUtils
open Format

let parse_cfunc fname body params retty =
  try
    (* let _ =
         List.iter (fun ps -> print_endline (AClightDebug.dbg_pstmt' ps)) body;
         print_endline ""
       in *)
    let body = List.concat (List.map deseq body) in
    let body = List.map (convert_pstmt AParse.parse_assertion) body in
    let body =
      List.filter (function Clight.PSdecl _ -> false | _ -> true) body
    in
    (* List.iter (fun ps -> print_endline (AClightDebug.dbg_pstmt ps)) body;
       print_endline ""; *)
    match
      AClightParser.concat_pstmts
        (fun n a -> AAst.Exists (AAst.FreeV n, a))
        body
    with
    | None -> failwith "parse error: can not concat partial statements"
    | Some cfunc ->
        let cfunc = AClightnorm.norm_cfunction cfunc in
        let cfunc, env = ATriple.driver cfunc in
        (fname, params, retty, cfunc, env)
  with Failure s -> failwith (s ^ " in '" ^ fname ^ "'")

let parse_cfuncdecl fname spec params retty =
  let withs, pre, post, env = ATriple.driver_decl fname spec in
  (fname, params, retty, withs, pre, post, env)

let parse_all filename =
  let src = Parse.read_file filename in
  let pstmt_strs = List.map String.trim (String.split_on_char '$' src) in
  let pstmt_strs = List.filter (fun s -> String.length s <> 0) pstmt_strs in
  let pairs = List.map parse_pstmt pstmt_strs in
  let pairs, _ = map_accum_l transform_pstmt SSet.empty pairs in
  let func_infos_rev = get_func_info pairs in
  let rec parse_aux decls defs = function
    | [] -> (decls, defs)
    | FuncDecl (fname, spec, params, retty) :: rest ->
        parse_aux (parse_cfuncdecl fname spec params retty :: decls) defs rest
    | FuncDef (fname, body, params, retty) :: rest ->
        parse_aux decls (parse_cfunc fname body params retty :: defs) rest
  in
  parse_aux [] [] func_infos_rev

let tuple_logicals env p =
  ExportAClight.separated_iter (ExportAClight.logical_var env p) (fun () ->
      fprintf p ", ")

let export_decl p (name, params, retty, withs, pre, post, env) =
  fprintf p "@[<v 2>Definition f_%s_spec_annotation :=@ %a.@]" name
    (ExportAClight.ForDecl.funcspec env)
    (withs, pre, post);
  fprintf p "@ @ ";
  fprintf p
    "@[<v 2>Definition f_%s_spec_complex :=@ ltac:(uncurry_funcspec \
     f_%s_spec_annotation).@]"
    name name;
  fprintf p "@ @ ";
  fprintf p "@[<v 2>Definition f_%s_funsig: funsig :=@ (%a, %a).@]" name
    (fun p params ->
      List.iter
        (fun (id, ty) ->
          fprintf p "(%ld%%positive, %a) :: " (Camlcoq.P.to_int32 id)
            ExportClight.typ ty)
        params;
      fprintf p "nil")
    params ExportClight.typ retty;
  fprintf p "@ @ ";
  fprintf p
    "@[<v 2>Definition %s_spec :=@ ltac:(make_funcspec _%s f_%s_funsig \
     f_%s_spec_complex).@]@ @ "
    name name name name;
  fprintf p "Lemma f_%s_precise (Delta: tycontext):@ " name;
  fprintf p "  precise_funspec Delta (snd %s_spec).@ " name;
  fprintf p "Proof.@ ";
  fprintf p "  prove_precise_funspec.@ ";
  fprintf p "Qed.@ @ ";
  fprintf p "Hint Resolve f_%s_precise: precise_spec.@ " name;
  fprintf p "@ "

let export_def p (func_name, params, retty, func, env) =
  let (AClight.Cfunc (withs, pre, post, body)) = func in
  fprintf p "@[<v 2>Definition f_%s_spec_annotation :=@ %a.@]" func_name
    (ExportAClight.funcspec env)
    (withs, pre, post);
  fprintf p "@ @ ";
  fprintf p
    "@[<v 2>Definition f_%s_spec_complex :=@ ltac:(uncurry_funcspec \
     f_%s_spec_annotation).@]"
    func_name func_name;
  fprintf p "@ @ ";
  fprintf p "@[<v 2>Definition f_%s_funsig: funsig :=@ (%a, %a).@]" func_name
    (fun p params ->
      List.iter
        (fun (id, ty) ->
          fprintf p "(%a, %a) :: " ExportClight.ident id ExportClight.typ ty)
        params;
      fprintf p "nil")
    params ExportClight.typ retty;
  fprintf p "@ @ ";
  fprintf p
    "@[<v 2>Definition %s_spec :=@ ltac:(make_funcspec _%s f_%s_funsig \
     f_%s_spec_complex).@]@ @ "
    func_name func_name func_name func_name;
  fprintf p "Lemma f_%s_precise (Delta: tycontext):@ " func_name;
  fprintf p "  precise_funspec Delta (snd %s_spec).@ " func_name;
  fprintf p "Proof.@ ";
  fprintf p "  prove_precise_funspec.@ ";
  fprintf p "Qed.@ @ ";
  fprintf p "Hint Resolve f_%s_precise: precise_spec.@ " func_name;
  fprintf p "@ ";
  fprintf p
    "@[<v 2>Definition f_%s_hint (para: GET_PARA_TYPE f_%s_spec_annotation) \
     :=@ match para with %a =>@ %a@]@ "
    func_name func_name
    (fun p -> function
      | [] -> fprintf p "tt"
      | ids ->
          fprintf p "(";
          tuple_logicals env p ids;
          fprintf p ")")
    withs (ExportAClight.cstmt env) body;
  fprintf p "  end.@ ";
  fprintf p "@ "

let export_delta_notation p func_name =
  fprintf p
    "Notation \"'Delta_specs_%s'\" := (DELTA_SPECS (f_%s, Vprog, Gprog))."
    func_name func_name;
  fprintf p "@ @ ";
  fprintf p
    "Notation \"'Delta_%s' DS\" := (DELTA (f_%s, Vprog, Gprog, @nil (ident * \
     Annotation), DS)) (at level 99)."
    func_name func_name;
  fprintf p "@ @ "

let export_annot p (mod_path, fdecls, fdefs) =
  fprintf p "@[<v 0>";
  fprintf p "From Coq Require Import String List ZArith.@ ";
  fprintf p
    "From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight \
     Clightdefs.@ ";
  fprintf p "Require Import Csplit.semantics.@ ";
  fprintf p "Require Import utils.AClightNotations.@ ";
  fprintf p "Require VST.floyd.proofauto.@ ";
  fprintf p "Require Import FloydSeq.precise_proofauto.@ ";
  fprintf p "Require Import FloydSeq.proofauto.@ ";
  fprintf p "Require Import Csplit.model_lemmas.@ ";
  fprintf p "Require Import Csplit.strong.@ ";
  fprintf p "Require Import FloydSeq.client_lemmas.@ ";
  fprintf p "Require Import Csplit.strongSoundness.@ ";
  fprintf p "Require Import Csplit.AClightFunc.@ ";
  fprintf p "Local Open Scope Z_scope.@ ";
  fprintf p "Import AClightNotations.@ ";
  fprintf p "Require Import %s.program.@ " mod_path;
  fprintf p "Require Import %s.definitions.@ " mod_path;
  fprintf p "Definition ___return := ret_temp.@ ";
  fprintf p "@ ";
  List.iter (export_decl p) fdecls;
  List.iter (export_def p) fdefs;
  fprintf p "@[<v 2>Definition Gprog : funspecs :=@ ltac:(with_library prog (";
  List.iter
    (fun (name, _, _, _, _, _, _) -> fprintf p "%s_spec :: " name)
    fdecls;
  List.iter (fun (name, _, _, _, _) -> fprintf p "%s_spec :: " name) fdefs;
  fprintf p "nil)).@]";
  fprintf p "@ @ ";
  List.iter (fun (name, _, _, _, _) -> export_delta_notation p name) fdefs;
  fprintf p "@]"

let export_path_header p mod_path =
  fprintf p "@[<v 0>";
  fprintf p "From Coq Require Import String List ZArith.@ ";
  fprintf p
    "From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight \
     Clightdefs.@ ";
  fprintf p "Require Import Csplit.semantics.@ ";
  fprintf p "Require Import utils.AClightNotations.@ ";
  fprintf p "Require VST.floyd.proofauto.@ ";
  fprintf p "Require Import FloydSeq.proofauto.@ ";
  fprintf p "Require Import Csplit.strong.@ ";
  fprintf p "Require Import FloydSeq.client_lemmas.@ ";
  fprintf p "Require Import Csplit.strongSoundness.@ ";
  fprintf p "Require Import Csplit.AClightFunc.@ ";
  fprintf p "Local Open Scope Z_scope.@ ";
  fprintf p "Import AClightNotations.@ ";
  fprintf p "Require Import %s.program.@ " mod_path;
  fprintf p "Require Import %s.definitions.@ " mod_path;
  fprintf p "Require Import %s.annotation.@ " mod_path;
  fprintf p "Import compcert.cfrontend.Clight.@ ";
  fprintf p "@]@ "

let export_path p (mod_path, func_name, env) path =
  export_path_header p mod_path;
  fprintf p
    "@[<v 2>Definition functional_correctness_statement: Prop :=@ %a.@]@."
    (ExportAClight.full_path (func_name, env))
    path

let export_normal_exit_path p (mod_path, func_name, env) path =
  export_path_header p mod_path;
  fprintf p
    "@[<v 2>Definition functional_correctness_statement: Prop :=@ %a.@]@."
    (ExportAClight.full_normal_exit_path (func_name, env))
    path

let export_ret_path p (mod_path, func_name, rettyp, env) path =
  export_path_header p mod_path;
  fprintf p
    "@[<v 2>Definition functional_correctness_statement: Prop :=@ %a.@]@."
    (ExportAClight.full_ret_path (func_name, rettyp, env))
    path

let export_empty_path_verif p (mod_path, func_name) path_name =
  fprintf p "@[<v 0>Require Import utils.VSTALib.@ ";
  fprintf p "@ ";
  fprintf p "Require Import %s.program.@ " mod_path;
  fprintf p "Require Import %s.definitions.@ " mod_path;
  fprintf p "Require Import %s.annotation.@ " mod_path;
  fprintf p "Require %s.%s.%s.@ " mod_path func_name path_name;
  fprintf p "@ ";
  fprintf p "Module SH_Proof <: STRAIGHTLINE_HOARE_TRIPLE_PROOF.@ ";
  fprintf p "@ ";
  fprintf p "Include %s.%s.%s.@ " mod_path func_name path_name;
  fprintf p "@ ";
  fprintf p "Theorem proof: functional_correctness_statement.@ ";
  fprintf p "Proof.@ ";
  fprintf p "  cbv delta [functional_correctness_statement].@ ";
  fprintf p "Admitted.@ ";
  fprintf p "@ ";
  fprintf p "End SH_Proof.@]@."

let export_empty_verif p (mod_path, func_name) path_names =
  fprintf p "@[<v 0>Require Import utils.VSTALib.@ ";
  fprintf p "@ ";
  fprintf p "Require Import %s.program.@ " mod_path;
  fprintf p "Require Import %s.definitions.@ " mod_path;
  fprintf p "Require Import %s.annotation.@ " mod_path;
  List.iter
    (fun path_name ->
      fprintf p "Require %s.%s.%s_verif.@ " mod_path func_name path_name)
    path_names;
  fprintf p "@ ";
  fprintf p "Theorem f_%s_functionally_correct :@ " func_name;
  fprintf p "  semax_body Vprog Gprog f_%s %s_spec.@ " func_name func_name;
  fprintf p "Proof.@ ";
  fprintf p "  VST_A_start_function f_%s_hint.@ " func_name;
  List.iter
    (fun path_name ->
      fprintf p "  + apply %s_verif.SH_Proof.proof.@ " path_name)
    path_names;
  fprintf p "Qed.@]@."

let export_func_pathes mod_path (func_name, params, retty, func, env) =
  let ex id a = PLSDef.Aex (id, a) in
  let ff = PLSDef.Anormal ([ PLSDef.FF ], [], []) in
  let goals =
    match retty with
    | Ctypes.Tvoid -> AClight.proof_goals_void_return ex ff func
    | _ -> AClight.proof_goals ex ff func
  in
  match goals with
  | None -> failwith ("can not generate proof goals for " ^ func_name)
  | Some ((pathes, normal_exit_paths), ret_pathes) ->
      let normal_path_num = List.length pathes in
      ensure_directory func_name;
      List.iteri
        (fun i path ->
          let st_chan =
            open_out (func_name ^ "/path" ^ string_of_int i ^ ".v")
          in
          export_path
            (formatter_of_out_channel st_chan)
            (mod_path, func_name, env) path;
          close_out st_chan)
        pathes;
      List.iteri
        (fun i path ->
          let st_chan =
            open_out
              (func_name ^ "/path" ^ string_of_int (i + normal_path_num) ^ ".v")
          in
          export_normal_exit_path
            (formatter_of_out_channel st_chan)
            (mod_path, func_name, env) path;
          close_out st_chan)
        normal_exit_paths;
      List.iteri
        (fun i path ->
          let st_chan =
            open_out (func_name ^ "/ret_path" ^ string_of_int i ^ ".v")
          in
          export_ret_path
            (formatter_of_out_channel st_chan)
            (mod_path, func_name, retty, env)
            path;
          close_out st_chan)
        ret_pathes;
      let path_num = normal_path_num + List.length normal_exit_paths in
      let ret_path_num = List.length ret_pathes in
      let path_names =
        List.init path_num (fun i -> "path" ^ string_of_int i)
        @ List.init ret_path_num (fun i -> "ret_path" ^ string_of_int i)
      in
      List.iter
        (fun path_name ->
          let path_verif = func_name ^ "/" ^ path_name ^ "_verif.v" in
          if not (Sys.file_exists path_verif) then (
            let verif_chan = open_out path_verif in
            export_empty_path_verif
              (formatter_of_out_channel verif_chan)
              (mod_path, func_name) path_name;
            close_out verif_chan))
        path_names;
      let verif = func_name ^ "/verif.v" in
      if not (Sys.file_exists verif) then (
        let verif_chan = open_out verif in
        export_empty_verif
          (formatter_of_out_channel verif_chan)
          (mod_path, func_name) path_names;
        close_out verif_chan);
      (func_name, path_num, ret_path_num)

let () =
  Printexc.record_backtrace true;
  Frontend.init ();
  if Array.length Sys.argv <> 2 then (
    printf "Usage: %s <'$' separated partial statements file>\n" Sys.argv.(0);
    exit 0)
  else
    let sourcefile = Sys.argv.(1) in
    let fdecls, fdefs = parse_all sourcefile in
    let dir_path = List.hd (String.split_on_char '.' sourcefile) in
    ensure_directory dir_path;
    Sys.chdir dir_path;
    let mod_path = String.split_on_char '/' dir_path in
    let source_base_name = List.hd (List.rev mod_path) in
    let mod_path = String.concat "." mod_path in
    let annot_chan = open_out "annotation.v" in
    let fdefs =
      List.map
        (fun (func_name, params, retty, func, env) ->
          let env, func = ExportAClight.lift_pre_exs env func in
          ExportAClight.name_function func;
          (func_name, params, retty, func, env))
        fdefs
    in
    export_annot (formatter_of_out_channel annot_chan) (mod_path, fdecls, fdefs);
    close_out annot_chan;
    let path_infos = List.map (export_func_pathes mod_path) fdefs in
    let func_names = List.map (fun (f, _, _, _, _) -> f) fdefs in
    let cprog_funcs =
      List.map (fun f -> source_base_name ^ "/" ^ f) func_names
    in
    let cprog_pathes =
      path_infos
      |> List.map (fun (f, pn, retn) ->
             List.init pn (fun i ->
                 String.concat "/"
                   [ source_base_name; f; "path" ^ string_of_int i ])
             @ List.init retn (fun i ->
                   String.concat "/"
                     [ source_base_name; f; "ret_path" ^ string_of_int i ]))
      |> List.concat
    in
    let config_chan = open_out "Makefile.config" in
    output_string config_chan
      ("CPROG_FUNCS += " ^ String.concat " " cprog_funcs ^ "\n");
    output_string config_chan
      ("CPROG_PATHS += " ^ String.concat " " cprog_pathes ^ "\n");
    close_out config_chan

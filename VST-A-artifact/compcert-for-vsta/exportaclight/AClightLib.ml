module SMap = Map.Make (String)
module SSet = Set.Make (String)
module IDMap = Map.Make (Camlcoq.P)
module IDSet = Set.Make (Camlcoq.P)

type ident = BinNums.positive

let opt_map f = function None -> None | Some a -> Some (f a)

let rec map_accum_l f acc = function
  | [] -> ([], acc)
  | x :: xs ->
      let x, acc1 = f acc x in
      let xs, acc2 = map_accum_l f acc1 xs in
      (x :: xs, acc2)

let ensure_directory dir =
  if Sys.file_exists dir then
    if Sys.is_directory dir then ()
    else failwith (dir ^ " exists but is not a directory")
  else
    let retc = Sys.command ("mkdir -m 755 " ^ dir) in
    if retc = 0 then ()
    else failwith ("can not create directory " ^ dir ^ " with 755 mode")

let hashtbl_find_exn tbl key =
  match Hashtbl.find_opt tbl key with
  | Some v -> v
  | None -> failwith ("Undefined '" ^ key ^ "'")

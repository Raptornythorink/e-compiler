open Batteries
open Rtl
open Linear
open Prog
open Utils
open Report
open Linear_print
open Options
open Linear_liveness

let succs_of_rtl_instr (i: rtl_instr) =
  match i with
  | Rtl.Rbranch (_, _, _, s1) -> [s1]
  | Rtl.Rjmp s -> [s]
  | _ -> []

let succs_of_rtl_instrs il : int list =
  List.concat (List.map succs_of_rtl_instr il)

(* effectue un tri topologique des blocs.  *)
let sort_blocks (nodes: (reg, rtl_instr list) Hashtbl.t) (entry:reg) =
  let rec add_block order n = match Hashtbl.find_option nodes n with 
   |None -> failwith "no instr for this reg"
   |Some rtl_instr_list -> let succs = succs_of_rtl_instrs rtl_instr_list in 
                          List.fold_left ( fun acc succ_n ->
                            if List.mem succ_n acc then acc
                            else add_block acc succ_n
                          ) (order@[n]) (List.rev succs)
in add_block [] entry

(* Supprime les jumps inutiles (Jmp à un label défini juste en dessous). *)
let rec remove_useless_jumps (l: rtl_instr list) = 
   match l with
|[] -> l
|(Rjmp lab)::(Rlabel lab')::q when lab=lab' -> (Rlabel lab)::(remove_useless_jumps q)
|r::q -> r::(remove_useless_jumps q)

(* Remove labels that are never jumped to. *)
let remove_useless_labels (l: rtl_instr list) =
   List.filter (fun instr -> match instr with 
    |Rlabel n  -> List.exists (fun i -> match i with 
                |Rjmp m when m=n -> true 
                |Rbranch (_,_,_,m) when m=n -> true
                | _ -> false
                ) l
    | _ -> true
   ) l 

let linear_of_rtl_fun
    ({ rtlfunargs; rtlfunbody; rtlfunentry; rtlfuninfo }: rtl_fun) =
  let block_order = sort_blocks rtlfunbody rtlfunentry in
  let linearinstrs =
    Rjmp rtlfunentry ::
    List.fold_left (fun l n ->
        match Hashtbl.find_option rtlfunbody n with
        | None -> l
        | Some li -> l @ Rlabel(n) :: li
      ) [] block_order in
  { linearfunargs = rtlfunargs;
    linearfunbody =
      linearinstrs |> remove_useless_jumps |> remove_useless_labels;
    linearfuninfo = rtlfuninfo;
  }

let linear_of_rtl_gdef = function
    Gfun f -> Gfun (linear_of_rtl_fun f)

let linear_of_rtl r =
  assoc_map linear_of_rtl_gdef r

let pass_linearize rtl =
  let linear = linear_of_rtl rtl in
  let lives = liveness_linear_prog linear in
  dump !linear_dump (fun oc -> dump_linear_prog oc (Some lives)) linear
    (fun file () -> add_to_report "linear" "Linear" (Code (file_contents file)));
  OK (linear, lives)

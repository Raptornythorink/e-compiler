open BatList
open Batteries
open Prog
open Utils
open Cfg
open Report
open Cfg_print
open Options

(* Élimination des NOPs. *)

(* [nop_transitions cfg] donne la liste des transitions NOP dans un CFG.

   Si le nœud [n] contient [Cnop s], alors [(n,s)] devrait être dans le résultat.
*)
let nop_transitions (cfgfunbody: (int, cfg_node) Hashtbl.t) : (int * int) list =
   Hashtbl.fold (fun n node acc ->
      match node with
      | Cnop(s) -> (n, s)::acc
      | _ -> acc
   ) cfgfunbody []

(* [follow n l visited] donne le premier successeur à partir de [n] qui ne soit
   pas un NOP. Pour connaître le successeur d'un nœud NOP, on utilisara la liste
   [l] telle que produite précédemment. Pour rappel [(x,y)] dans [l] signifie
   qu'il y a un transition depuis un nœud [x] qui contient une instruction [Cnop
   y].

   L'ensemble [visited] est utilisé pour éviter les boucles.
   *)
let rec follow (n: int) (l: (int * int) list) (visited: int Set.t) : int =
   match l with
   | [] -> n
   | (x, y)::q ->
      if x = n then
         if Set.mem y visited then n
         else follow y l (Set.add y visited)
      else follow n q visited

(* [nop_transitions_closed] contient la liste [(n,s)] telle que l'instruction au
   nœud [n] est le début d'une chaîne de NOPs qui termine au nœud [s]. Les
   enseignants du cours de compiilation sont heureux de vous offrir cette
   fonction. *)
let nop_transitions_closed cfgfunbody =
  List.map (fun (node_id, node) ->
      (node_id, follow node_id (nop_transitions cfgfunbody) Set.empty))
    (nop_transitions cfgfunbody)

(* Nous allons maintenant réécrire notre programme pour remplacer les
   successeurs [s] de chaque nœud du CFG de la manière suivante : si [s] est le
   début d'une chaîne de NOPs, on remplace [s] par la fin de cette chaîne, en
   éliminant ainsi les nœuds NOPs. *)

(* [replace_succ nop_succs s] donne le nouveau nom du nœud [s], en utilisant la
   liste [nop_succs] (telle que renvoyée par [nop_transitions_closed]). *)
let replace_succ nop_succs s =
   match List.assoc_opt s nop_succs with
   | None -> s
   | Some s' -> s'

(* [replace_succs nop_succs n] remplace le nœud [n] par un nœud équivalent où on
   a remplacé les successeurs, en utilisant la liste [nop_succs]. *)
let replace_succs nop_succs (n: cfg_node) =
   match n with
   | Cnop(s) -> Cnop(replace_succ nop_succs s)
   | _ -> n

(* [nop_elim_fun f] applique la fonction [replace_succs] à chaque nœud du CFG. *)
let nop_elim_fun ({ cfgfunargs; cfgfunbody; cfgentry } as f: cfg_fun) =
  let nop_transf = nop_transitions_closed cfgfunbody in
  (* On utilise la fonction [Hashtbl.filter_map f h] qui permet d'appliquer une
     fonction à chaque nœud de [h] et d'éliminer ceux pour lesquels [f] renvoie
     [None].

     On souhaite éliminer les nœuds qui n'ont pas de prédécesseurs
     (inaccessibles), et appliquer la fonction [replace_succs] aux nœuds qui
     resteront.
  *)
   let new_cfgentry = replace_succ nop_transf cfgentry in
   let new_cfgfunbody = Hashtbl.map (fun n node -> replace_succs nop_transf node) cfgfunbody in
   Hashtbl.filter_map_inplace (
      fun n node -> if (n <> new_cfgentry && Set.is_empty (preds new_cfgfunbody n)) then None else Some node
      ) new_cfgfunbody;

  (* La fonction renvoyée est composée du nouveau [cfgfunbody] que l'on vient de
     calculer, et le point d'entrée est transformé en conséquence. *)
  {f with cfgfunbody = new_cfgfunbody; cfgentry = new_cfgentry }

let nop_elim_gdef gd =
  match gd with
    Gfun f -> Gfun (nop_elim_fun f)

let nop_elimination cp =
  if !Options.no_cfg_ne
  then cp
  else assoc_map nop_elim_gdef cp

let pass_nop_elimination cfg =
  let cfg = nop_elimination cfg in
  record_compile_result "NopElim";
  dump (!cfg_dump >*> fun s -> s ^ "3") dump_cfg_prog cfg
    (call_dot "cfg-after-nop" "CFG after NOP elim");
  OK cfg

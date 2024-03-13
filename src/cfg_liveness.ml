open Batteries
open Cfg

(* Analyse de vivacité *)

(* [vars_in_expr e] renvoie l'ensemble des variables qui apparaissent dans [e]. *)
let rec vars_in_expr (e: expr) : string Set.t = match e with
   | Ebinop (binop, e1, e2) -> Set.union (vars_in_expr e1) (vars_in_expr e2)
   | Eunop (unop, e) -> vars_in_expr e
   | Eint i -> Set.empty
   | Evar s -> Set.singleton s

(* [live_after_node cfg n] renvoie l'ensemble des variables vivantes après le
   nœud [n] dans un CFG [cfg]. [lives] est l'état courant de l'analyse,
   c'est-à-dire une table dont les clés sont des identifiants de nœuds du CFG et
   les valeurs sont les ensembles de variables vivantes avant chaque nœud. *)
let live_after_node 
   (cfg: (int,cfg_node) Hashtbl.t) (n:int) 
   (lives: (int, string Set.t) Hashtbl.t) 
   : string Set.t =
   let succs_n = succs cfg n in 
   Set.fold (fun s acc -> match Hashtbl.find_option lives s with
      | None -> acc
      | Some set_s -> Set.union acc set_s
   ) succs_n Set.empty

(* [live_cfg_node node live_after] renvoie l'ensemble des variables vivantes
   avant un nœud [node], étant donné l'ensemble [live_after] des variables
   vivantes après ce nœud. *)
let live_cfg_node (node: cfg_node) (live_after: string Set.t) =
   match node with
   | Cassign (s, e, n) -> Set.union (Set.remove s live_after) (vars_in_expr e)
   | Creturn e -> Set.union live_after (vars_in_expr e)
   | Cprint (e, n) -> Set.union live_after (vars_in_expr e) 
   | Ccmp (e, n1, n2) -> Set.union live_after (vars_in_expr e)
   | Cnop node1 -> live_after

(* [live_cfg_nodes cfg lives] effectue une itération du calcul de point fixe.

   Cette fonction met à jour l'état de l'analyse [lives] et renvoie un booléen
   qui indique si le calcul a progressé durant cette itération (i.e. s'il existe
   au moins un nœud n pour lequel l'ensemble des variables vivantes avant ce
   nœud a changé). *)
let live_cfg_nodes (cfg: (int,cfg_node) Hashtbl.t) (lives : (int, string Set.t) Hashtbl.t) : bool =
   Hashtbl.fold (fun node cfg_node acc ->
      let live_after = live_after_node cfg node lives in 
      let live_before_node= live_cfg_node cfg_node live_after in
      match Hashtbl.find_option lives node with
      |None -> Hashtbl.replace lives node live_before_node; true
      |Some set_living ->Hashtbl.replace lives node (Set.union set_living live_before_node) ; 
            acc ||not(Set.equal (Set.union live_before_node set_living) set_living)
   ) cfg false

(* [live_cfg_fun f] calcule l'ensemble des variables vivantes avant chaque nœud
   du CFG en itérant [live_cfg_nodes] jusqu'à ce qu'un point fixe soit atteint.
   *)
let live_cfg_fun (f: cfg_fun) : (int, string Set.t) Hashtbl.t =
  let lives = Hashtbl.create 17 in
  let cfg = f.cfgfunbody in
  let rec liveness lives' =
      match live_cfg_nodes cfg lives' with
      | false -> lives'
      | true -> liveness lives'
   in liveness lives

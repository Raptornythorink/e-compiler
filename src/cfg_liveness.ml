open Batteries
open Cfg

(* Analyse de vivacité *)

(* [vars_in_expr e] renvoie l'ensemble des variables qui apparaissent dans [e]. *)
let rec vars_in_expr (e: expr) =
   match e with
   | Evar(var) -> Set.singleton var
   | Eint(_) -> Set.empty
   | Eunop(_, e) -> vars_in_expr e
   | Ebinop(_, e1, e2) -> Set.union (vars_in_expr e1) (vars_in_expr e2)
   | Ecall(_, args) -> List.fold_left (fun acc e -> Set.union acc (vars_in_expr e)) Set.empty args
   | Estk(_) -> Set.empty
   | Eload(e, _) -> vars_in_expr e

(* [live_after_node cfg n] renvoie l'ensemble des variables vivantes après le
   nœud [n] dans un CFG [cfg]. [lives] est l'état courant de l'analyse,
   c'est-à-dire une table dont les clés sont des identifiants de nœuds du CFG et
   les valeurs sont les ensembles de variables vivantes avant chaque nœud. *)
let live_after_node cfg n (lives: (int, string Set.t) Hashtbl.t) : string Set.t =
   Set.fold (fun succ acc -> Set.union acc (match (Hashtbl.find_option lives succ) with None -> Set.empty | Some s -> s)) (succs cfg n) Set.empty

(* [live_cfg_node node live_after] renvoie l'ensemble des variables vivantes
   avant un nœud [node], étant donné l'ensemble [live_after] des variables
   vivantes après ce nœud. *)
let live_cfg_node (node: cfg_node) (live_after: string Set.t) =
   match node with
   | Cassign(v, e, _) -> Set.union (vars_in_expr e) (Set.remove v live_after)
   | Creturn(e) -> Set.union (vars_in_expr e) live_after
   | Ccmp(e, _, _) -> Set.union (vars_in_expr e) live_after
   | Cnop(_) -> live_after
   | Ccall(f, args, _) -> Set.union (vars_in_expr (Ecall(f, args))) live_after
   | Cstore(addr, v, _, _) -> Set.union (vars_in_expr v) (Set.union (vars_in_expr addr) live_after)

(* [live_cfg_nodes cfg lives] effectue une itération du calcul de point fixe.

   Cette fonction met à jour l'état de l'analyse [lives] et renvoie un booléen
   qui indique si le calcul a progressé durant cette itération (i.e. s'il existe
   au moins un nœud n pour lequel l'ensemble des variables vivantes avant ce
   nœud a changé). *)
let live_cfg_nodes cfg (lives : (int, string Set.t) Hashtbl.t) =
   let changed = ref false in
   Hashtbl.iter (fun n node -> 
      let old_live_before =
         match Hashtbl.find_option lives n with
         | None -> Set.empty
         | Some s -> s in
      let live_after = live_after_node cfg n lives in
      let live_before = live_cfg_node (Hashtbl.find cfg n) live_after in
      if not (Set.equal live_before old_live_before) then begin
         changed := true;
         Hashtbl.replace lives n live_before
      end
      ) cfg;
   !changed

(* [live_cfg_fun f] calcule l'ensemble des variables vivantes avant chaque nœud
   du CFG en itérant [live_cfg_nodes] jusqu'à ce qu'un point fixe soit atteint.
   *)
let live_cfg_fun (f: cfg_fun) : (int, string Set.t) Hashtbl.t =
  let lives = Hashtbl.create 17 in
  let over = ref false in
  while not !over do
      over := not (live_cfg_nodes f.cfgfunbody lives)
  done;
  lives

open Batteries
open Elang
open Cfg
open Rtl
open Prog
open Utils
open Report
open Rtl_print
open Options

(* Une partie de la génération de RTL consiste à allouer les variables dans des
   pseudo-registres RTL.

   Ces registres sont en nombre illimité donc ce problème est facile.

   Étant donnés :
   - [next_reg], le premier numéro de registre disponible (pas encore alloué à
   une variable)
   - [var2reg], une liste d'associations dont les clés sont des variables et les
   valeurs des numéros de registres
   - [v] un nom de variable (de type [string]),

   [find_var (next_reg, var2reg) v] renvoie un triplet [(r, next_reg, var2reg)]:

   - [r] est le registre RTL associé à la variable [v]
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.

*)
let find_var (next_reg, var2reg) v =
  match List.assoc_opt v var2reg with
    | Some r -> (r, next_reg, var2reg)
    | None -> (next_reg, next_reg + 1, assoc_set var2reg v next_reg)

(* [rtl_instrs_of_cfg_expr (next_reg, var2reg) e] construit une liste
   d'instructions RTL correspondant à l'évaluation d'une expression E.

   Le retour de cette fonction est un quadruplet [(r,l,next_reg,var2reg)], où :
   - [r] est le registre RTL dans lequel le résultat de l'évaluation de [e] aura
     été stocké
   - [l] est une liste d'instructions RTL.
   - [next_reg] est le nouveau premier registre disponible
   - [var2reg] est la nouvelle association nom de variable/registre.
*)
let rec rtl_instrs_of_cfg_expr (next_reg, var2reg) (e: expr) =
  match e with
    | Eint(i) -> (next_reg, [Rconst(next_reg, i)], next_reg + 1, var2reg)
    | Evar(v) -> let r1, next_reg1, var2reg1 = find_var (next_reg, var2reg) v in
                 (r1, [], next_reg1, var2reg1)
    | Eunop(u, e) -> let r1, l1, next_reg1, var2reg1 = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
                     (next_reg1, l1 @ [Runop(u, next_reg1, r1)], next_reg1 + 1, var2reg1)
    | Ebinop(b, e1, e2) -> let r1, l1, next_reg1, var2reg1 = rtl_instrs_of_cfg_expr (next_reg, var2reg) e1 in
                           let r2, l2, next_reg2, var2reg2 = rtl_instrs_of_cfg_expr (next_reg1, var2reg1) e2 in
                           (next_reg2, l1 @ l2 @ [Rbinop(b, next_reg2, r1, r2)], next_reg2 + 1, var2reg2)
    | Ecall(f, args) -> let (rargs, largs, next_reg1, var2reg1) = List.fold_left (
                             fun (rargs, largs, next_reg, var2reg) arg ->
                               let (r, l, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) arg in
                               (rargs @ [r], largs @ l, next_reg, var2reg)
                             ) ([], [], next_reg, var2reg) args in
                         (next_reg1, largs @ [Rcall(Some(next_reg1), f, rargs)], next_reg1 + 1, var2reg1)
    | Estk(i) -> (next_reg, [Rstk(next_reg, i)], next_reg + 1, var2reg)
    | Eload(e, sz) -> let r1, l1, next_reg1, var2reg1 = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
                      (next_reg1, l1 @ [Rload(next_reg1, r1, sz)], next_reg1 + 1, var2reg1)

let is_cmp_op =
  function Eclt -> Some Rclt
         | Ecle -> Some Rcle
         | Ecgt -> Some Rcgt
         | Ecge -> Some Rcge
         | Eceq -> Some Rceq
         | Ecne -> Some Rcne
         | _ -> None

let rtl_cmp_of_cfg_expr (e: expr) =
  match e with
  | Ebinop (b, e1, e2) ->
    (match is_cmp_op b with
     | None -> (Rcne, e, Eint 0)
     | Some rop -> (rop, e1, e2))
  | _ -> (Rcne, e, Eint 0)


let rtl_instrs_of_cfg_node ((next_reg:int), (var2reg: (string*int) list)) (c: cfg_node) =
  match c with
    | Cnop(s) -> ([Rjmp(s)], next_reg, var2reg)
    | Creturn(e) -> let r1, l1, next_reg1, var2reg1 = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
                    (l1 @ [Rret(r1)], next_reg1, var2reg1)
    | Ccmp(e, s1, s2) -> let cmp, e1, e2 = rtl_cmp_of_cfg_expr e in
                         let r1, l1, next_reg1, var2reg1 = rtl_instrs_of_cfg_expr (next_reg, var2reg) e1 in
                         let r2, l2, next_reg2, var2reg2 = rtl_instrs_of_cfg_expr (next_reg1, var2reg1) e2 in
                         (l1 @ l2 @ [Rbranch(cmp, r1, r2, s1); Rjmp(s2)], next_reg2, var2reg2)
    | Cassign(v, e, s) -> let r1, l1, next_reg1, var2reg1 = rtl_instrs_of_cfg_expr (next_reg, var2reg) e in
                          let r2, next_reg2, var2reg2 = find_var (next_reg1, var2reg1) v in
                          (l1 @ [Rmov(r2, r1); Rjmp(s)], next_reg2, var2reg2)
    | Ccall(f, args, s) -> let rargs, largs, next_reg1, var2reg1 = List.fold_left (
                              fun (rargs, largs, next_reg, var2reg) arg ->
                                let (r, l, next_reg, var2reg) = rtl_instrs_of_cfg_expr (next_reg, var2reg) arg in
                                (rargs @ [r], largs @ l, next_reg, var2reg)
                              ) ([], [], next_reg, var2reg) args in
                          (largs @ [Rcall(None, f, rargs); Rjmp(s)], next_reg1, var2reg1)
    | Cstore(addr, v, sz, succ) -> let r1, l1, next_reg1, var2reg1 = rtl_instrs_of_cfg_expr (next_reg, var2reg) addr in
                                   let r2, l2, next_reg2, var2reg2 = rtl_instrs_of_cfg_expr (next_reg1, var2reg1) v in
                                   (l1 @ l2 @ [Rstore(r1, r2, sz); Rjmp(succ)], next_reg2, var2reg2)

let rtl_instrs_of_cfg_fun cfgfunname ({ cfgfunargs; cfgfunbody; cfgentry; cfgfunstksz }: cfg_fun) =
  let (rargs, next_reg, var2reg) =
    List.fold_left (fun (rargs, next_reg, var2reg) a ->
        let (r, next_reg, var2reg) = find_var (next_reg, var2reg) a in
        (rargs @ [r], next_reg, var2reg)
      )
      ([], 0, []) cfgfunargs
  in
  let rtlfunbody = Hashtbl.create 17 in
  let (next_reg, var2reg) = Hashtbl.fold (fun n node (next_reg, var2reg)->
      let (l, next_reg, var2reg) = rtl_instrs_of_cfg_node (next_reg, var2reg) node in
      Hashtbl.replace rtlfunbody n l;
      (next_reg, var2reg)
    ) cfgfunbody (next_reg, var2reg) in
  {
    rtlfunargs = rargs;
    rtlfunentry = cfgentry;
    rtlfunbody;
    rtlfuninfo = var2reg;
    rtlfunstksz = cfgfunstksz;
  }

let rtl_of_gdef funname = function
    Gfun f -> Gfun (rtl_instrs_of_cfg_fun funname f)

let rtl_of_cfg cp = List.map (fun (s, gd) -> (s, rtl_of_gdef s gd)) cp

let pass_rtl_gen cfg =
  let rtl = rtl_of_cfg cfg in
  dump !rtl_dump dump_rtl_prog rtl
    (fun file () -> add_to_report "rtl" "RTL" (Code (file_contents file)));
  OK rtl

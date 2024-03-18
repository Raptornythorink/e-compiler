open Elang
open Batteries
open Prog
open Utils
open Builtins

let binop_bool_to_int f x y = if f x y then 1 else 0

(* [eval_binop b x y] évalue l'opération binaire [b] sur les arguments [x]
   et [y]. *)
let eval_binop (b: binop) : int -> int -> int =
  match b with
   | Eadd -> fun x y -> x + y
   | Esub -> fun x y -> x - y
   | Emul -> fun x y -> x * y
   | Ediv -> fun x y -> x / y
   | Emod -> fun x y -> x mod y
   | Exor -> fun x y -> x lxor y
   | Eclt -> binop_bool_to_int (<)
   | Ecle -> binop_bool_to_int (<=)
   | Ecgt -> binop_bool_to_int (>)
   | Ecge -> binop_bool_to_int (>=)
   | Eceq -> binop_bool_to_int (=)
   | Ecne -> binop_bool_to_int (<>)

(* [eval_unop u x] évalue l'opération unaire [u] sur l'argument [x]. *)
let eval_unop (u: unop) : int -> int =
   fun x -> -x

(* [eval_eexpr st e] évalue l'expression [e] dans l'état [st]. Renvoie une
   erreur si besoin. *)
let rec eval_eexpr prog oc st (e : expr) : (int * int state) res=
   match e with
   | Ebinop(b, e1, e2) ->
      eval_eexpr prog oc st e1 >>=  fun (v1, st') ->
      eval_eexpr prog oc st' e2 >>=  fun (v2, st'') ->
      OK(eval_binop b v1 v2, st'')
   | Eunop(u, e) ->
      eval_eexpr prog oc st e >>= fun (v, st') ->
      OK(eval_unop u v, st')
   | Eint(i) -> OK(i, st)
   | Evar(v) -> (
      match Hashtbl.find_option st.env v with
      | Some v -> OK(v, st)
      | None -> Error(Format.sprintf "E: Variable %s not found.\n" v)
   )
   | Ecall(f, args) -> List.fold_left (fun acc e -> acc >>= fun (l, nst) -> eval_eexpr prog oc nst e >>= fun (v, nst') -> OK(l@[v], nst')) (OK([], st)) args >>= fun (eargs, st') ->
                        match find_function prog f with
                        | OK(fdef) -> eval_efun prog oc st' fdef f eargs >>= fun (v, st'') -> (
                           match v with
                           | Some v -> OK(v, st'')
                           | None -> Error("E: Function call did not return a value.\n")
                        )
                        | Error(_) -> do_builtin oc st'.mem f eargs >>= fun v' -> (
                           match v' with
                           | Some v -> OK(v, st')
                           | None -> Error("E: Function call did not return a value.\n")
                        )  

(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
and eval_einstr prog oc (st: int state) (ins: instr) :
  (int option * int state) res =
   match ins with
   | Iassign(v, e) ->
      eval_eexpr prog oc st e >>= fun (v', st') ->
      Hashtbl.replace st'.env v v';
      OK(None, st')
   | Iif(e, i1, i2) ->
      eval_eexpr prog oc st e >>= fun (v, st') ->
      if v <> 0 then
         eval_einstr prog oc st' i1
      else
         eval_einstr prog oc st' i2
   | Iwhile(e, i) -> 
      eval_eexpr prog oc st e >>= fun (v, st') ->
         if v <> 0 then
            eval_einstr prog oc st' i >>= fun (ret, st'') ->
            match ret with
            | Some v -> OK (Some v, st'')
            | None -> eval_einstr prog oc st'' ins
         else
            OK(None, st')
   | Iblock(il) -> 
      let rec eval_block st l = match l with
         | [] -> OK(None, st)
         | i::iq -> eval_einstr prog oc st i >>= fun (ret, st') ->
                     match ret with
                     | Some v -> OK(Some v, st')
                     | None -> eval_block st' iq
      in eval_block st il 
   | Ireturn(e) -> eval_eexpr prog oc st e >>= fun (v, st') -> OK(Some v, st')
   | Icall(f, args) -> List.fold_left (fun acc e -> acc >>= fun (l, nst) -> eval_eexpr prog oc nst e >>= fun (v, nst') -> OK(l@[v], nst')) (OK([], st)) args >>= fun (eargs, st') ->
                        match find_function prog f with
                        | OK(fdef) -> eval_efun prog oc st' fdef f eargs
                        | Error(_) -> do_builtin oc st'.mem f eargs >>= fun v -> OK(v, st')
(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
and eval_efun prog oc (st: int state) ({ funargs; funbody}: efun)
    (fname: string) (vargs: int list)
  : (int option * int state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restore l'environnement de l'appelant. *)
  let env_save = Hashtbl.copy st.env in
  let env = Hashtbl.create 17 in
  match List.iter2 (fun a v -> Hashtbl.replace env a v) funargs vargs with
  | () ->
    eval_einstr prog oc { st with env } funbody >>= fun (v, st') ->
    OK (v, { st' with env = env_save })
  | exception Invalid_argument _ ->
    Error (Format.sprintf
             "E: Called function %s with %d arguments, expected %d.\n"
             fname (List.length vargs) (List.length funargs)
          )

(* [eval_eprog oc ep memsize params] évalue un programme complet [ep], avec les
   arguments [params].

   Le paramètre [memsize] donne la taille de la mémoire dont ce programme va
   disposer. Ce n'est pas utile tout de suite (nos programmes n'utilisent pas de
   mémoire), mais ça le sera lorsqu'on ajoutera de l'allocation dynamique dans
   nos programmes.

   Renvoie:

   - [OK (Some v)] lorsque l'évaluation de la fonction a lieu sans problèmes et renvoie une valeur [v].

   - [OK None] lorsque l'évaluation de la fonction termine sans renvoyer de valeur.

   - [Error msg] lorsqu'une erreur survient.
   *)
let eval_eprog oc (ep: eprog) (memsize: int) (params: int list)
  : int option res =
  let st = init_state memsize in
  find_function ep "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length f.funargs in
  let params = take n params in
  eval_efun ep oc st f "main" params >>= fun (v, _) ->
  OK v

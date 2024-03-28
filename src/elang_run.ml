open Elang
open Elang_gen
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
let rec eval_eexpr prog oc typ_struct typ_var typ_fun (varinmem: (string, int) Hashtbl.t) (sp: int) (funstksz: int) (st: int state) (e: expr) : (int * int state) res=
   match e with
   | Ebinop(b, e1, e2) ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e1 >>=  fun (v1, st') ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st' e2 >>=  fun (v2, st'') ->
      (match type_expr typ_struct typ_var typ_fun e1, type_expr typ_struct typ_var typ_fun e2 with
         | OK(Tptr(t1)), OK(Tptr(t2)) ->
            OK(eval_binop b v1 v2, st'')
         | OK(Tptr(t)), _ ->
            size_type typ_struct t >>= fun size ->
            OK(eval_binop b v1 (size * v2), st'')
         | _, OK(Tptr(t)) ->
            size_type typ_struct t >>= fun size ->
            OK(eval_binop b (v1 * size) v2, st'')
         | _, _ -> OK(eval_binop b v1 v2, st'')
      )
   | Eunop(u, e) ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e >>= fun (v, st') ->
      OK(eval_unop u v, st')
   | Eint(i) -> OK(i, st)
   | Echar(c) -> OK(Char.code c, st)
   | Evar(v) -> (
      match Hashtbl.find_option varinmem v with
      | Some(offset) ->
         let t = Hashtbl.find typ_var v in
         size_type typ_struct t >>= fun size ->
         Mem.read_bytes_as_int st.mem offset size >>= fun v' ->
         OK(v', st)
      | None -> (
         match Hashtbl.find_option st.env v with
         | Some v' -> OK(v', st)
         | None -> Error(Format.sprintf "E: Variable %s not found.\n" v)
      )
   )
   | Eaddrof(e) -> (match e with
      | Evar(v) -> (
         match Hashtbl.find_option varinmem v with
         | Some(offset) -> OK(offset, st)
         | None -> Error(Format.sprintf "E: Variable %s not found.\n" v)
      )
      | Eload(e) -> eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e
      | _ -> Error("E: Cannot take the address of this expression.\n")
    )
   | Eload(addr) -> 
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st  addr >>= fun (v, st') ->
      type_expr typ_struct typ_var typ_fun addr >>= fun t ->
      (match t with
         | Tptr(t') ->
            size_type typ_struct t' >>= fun size ->
            Mem.read_bytes_as_int st'.mem v size >>= fun v' ->
            OK(v', st')
         | Ttab(t', n) ->
            size_type typ_struct t' >>= fun size ->
            Mem.read_bytes_as_int st'.mem (v + size * n) size >>= fun v' ->
            OK(v', st')
         | _ -> Error("E: Cannot load from this expression.\n")
      )
   | Ecall(f, args) -> 
      List.fold_left (fun acc e -> acc >>= fun (l, nst) -> eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz nst e >>= fun (v, nst') -> OK(l@[v], nst')) (OK([], st)) args >>= fun (eargs, st') ->
      (match find_function prog f with
         | OK(fdef) -> eval_efun prog oc typ_struct typ_fun (sp + funstksz) st' fdef f eargs >>= fun (v, st'') -> (
            match v with
            | Some v -> OK(v, st'')
            | None -> Error("E: Function call did not return a value.\n")
         )
         | Error(_) -> do_builtin oc st'.mem f eargs >>= fun v' -> (
            match v' with
            | Some v -> OK(v, st')
            | None -> Error("E: Function call did not return a value.\n")
         )
      )
   | Egetfield(e, f) -> 
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e >>= fun (v, st') ->
      type_expr typ_struct typ_var typ_fun e >>= fun t ->
      (match t with
         | Tptr(Tstruct(s)) -> (
            match Hashtbl.find_option typ_struct s with
            | Some(fields) -> (
               field_type typ_struct s f >>= fun t' ->
               (match t' with
               | Tint | Tchar | Tptr(_) -> 
                  size_type typ_struct t' >>= fun size ->
                  field_offset typ_struct s f >>= fun offset ->
                  Mem.read_bytes_as_int st'.mem (v + offset) size >>= fun v' ->
                  OK(v', st')
               | _ -> 
                  field_offset typ_struct s f >>= fun offset ->
                  OK(v + offset, st')
               )
            )
            | None -> Error(Format.sprintf "E: Struct %s not found.\n" s)
         )
         | _ -> Error("E: Cannot get field from this expression\n")
      )

(* [eval_einstr oc st ins] évalue l'instrution [ins] en partant de l'état [st].

   Le paramètre [oc] est un "output channel", dans lequel la fonction "print"
   écrit sa sortie, au moyen de l'instruction [Format.fprintf].

   Cette fonction renvoie [(ret, st')] :

   - [ret] est de type [int option]. [Some v] doit être renvoyé lorsqu'une
   instruction [return] est évaluée. [None] signifie qu'aucun [return] n'a eu
   lieu et que l'exécution doit continuer.

   - [st'] est l'état mis à jour. *)
and eval_einstr prog oc typ_struct typ_var typ_fun (varinmem: (string, int) Hashtbl.t) (sp: int) (funstksz: int) (st: int state) (ins: instr) :
  (int option * int state) res =
   match ins with
   | Iassign(v, e) ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e >>= fun (v', st') -> (
      match Hashtbl.find_option varinmem v with
      | Some(offset) ->
         let t = Hashtbl.find typ_var v in
         size_type typ_struct t >>= fun size ->
         Mem.write_bytes st'.mem offset (split_bytes size v') >>= fun _ ->
         OK(None, st')
      | None ->
         Hashtbl.replace st'.env v v';
         OK(None, st')
      )
   | Iif(e, i1, i2) ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e >>= fun (v, st') ->
      if v <> 0 then
         eval_einstr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st' i1
      else
         eval_einstr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st' i2
   | Iwhile(e, i) -> 
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e >>= fun (v, st') ->
         if v <> 0 then
            eval_einstr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st' i >>= fun (ret, st'') ->
            match ret with
            | Some v -> OK(Some v, st'')
            | None -> eval_einstr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st'' ins
         else
            OK(None, st')
   | Iblock(il) -> (
      match il with
      | [] -> OK(None, st)
      | i::iq ->
         eval_einstr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st i >>= fun (ret, st') ->
         match ret with
         | Some v -> OK(Some v, st')
         | None -> eval_einstr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st' (Iblock(iq))
   )
   | Ireturn(e) -> eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e >>= fun (v, st') -> OK(Some v, st')
   | Istore(addr, v) ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st addr >>= fun (addr', st') ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st' v >>= fun (v', st'') ->
      type_expr typ_struct typ_var typ_fun addr >>= fun t ->
      (match t with
         | Tptr(t') ->
            size_type typ_struct t' >>= fun size ->
            Mem.write_bytes st''.mem addr' (split_bytes size v') >>= fun _ ->
            OK(None, st'')
         | _ -> Error("E: Cannot store to this expression.\n")
      )
   | Icall(f, args) ->
      List.fold_left (fun acc e -> acc >>= fun (l, nst) -> eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz nst e >>= fun (v, nst') -> OK(l@[v], nst')) (OK([], st)) args >>= fun (eargs, st') ->
      (match find_function prog f with
      | OK(fdef) -> eval_efun prog oc typ_struct typ_fun (sp + funstksz) st' fdef f eargs >>= fun (_, st'') ->
         OK(None, st'')
      | Error(_) -> do_builtin oc st'.mem f eargs >>= fun _ -> OK(None, st')
      )
   | Isetfield(e, f, v) ->
      eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st e >>= fun (exp, st') ->
      type_expr typ_struct typ_var typ_fun e >>= fun t ->
      (match t with
         | Tptr(Tstruct(s)) -> (
            match Hashtbl.find_option typ_struct s with
            | Some(fields) -> (
               field_type typ_struct s f >>= fun t' ->
               size_type typ_struct t' >>= fun size ->
               field_offset typ_struct s f >>= fun offset ->
               eval_eexpr prog oc typ_struct typ_var typ_fun varinmem sp funstksz st' v >>= fun (v', st'') ->
               Mem.write_bytes st''.mem (exp + offset) (split_bytes size v') >>= fun _ ->
               OK(None, st'')
            )
            | None -> Error(Format.sprintf "E: Struct %s not found.\n" s)
         )
         | _ -> Error("E: Cannot set field from this expression\n")
      )
   

(* [eval_efun oc st f fname vargs] évalue la fonction [f] (dont le nom est
   [fname]) en partant de l'état [st], avec les arguments [vargs].

   Cette fonction renvoie un couple (ret, st') avec la même signification que
   pour [eval_einstr]. *)
and eval_efun prog oc typ_struct typ_fun (sp: int) (st: int state) ({ funargs; funbody; funvartype; funrettype; funvarinmem; funstksz}: efun)
    (fname: string) (vargs: int list)
  : (int option * int state) res =
  (* L'environnement d'une fonction (mapping des variables locales vers leurs
     valeurs) est local et un appel de fonction ne devrait pas modifier les
     variables de l'appelant. Donc, on sauvegarde l'environnement de l'appelant
     dans [env_save], on appelle la fonction dans un environnement propre (Avec
     seulement ses arguments), puis on restore l'environnement de l'appelant. *)
   let env_save = Hashtbl.copy st.env in
   let env = Hashtbl.create 17 in
   Hashtbl.replace typ_fun fname (List.map snd funargs, funrettype);
   match List.iter2 (fun a v -> Hashtbl.replace env (fst a) v) funargs vargs with
   | () ->
      eval_einstr prog oc typ_struct funvartype typ_fun funvarinmem sp funstksz { st with env } funbody >>= fun (v, st') ->
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
  find_function (fst ep) "main" >>= fun f ->
  (* ne garde que le nombre nécessaire de paramètres pour la fonction "main". *)
  let n = List.length f.funargs in
  let params = take n params in
  let fun_typ = Hashtbl.create 17 in
  Hashtbl.replace fun_typ "print" ([Tint], Tvoid);
  Hashtbl.replace fun_typ "print_int" ([Tint], Tvoid);
  Hashtbl.replace fun_typ "print_char" ([Tchar], Tvoid);
  eval_efun (fst ep) oc (snd ep) fun_typ 0 st f "main" params >>= fun (v, _) ->
  OK v

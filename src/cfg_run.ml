open Prog
open Elang
open Elang_run
open Batteries
open BatList
open Cfg
open Utils
open Builtins

let rec eval_cfgexpr prog oc st (e: expr) : (int * int state) res =
  match e with
  | Ebinop(b, e1, e2) ->
    eval_cfgexpr prog oc st e1 >>= fun (v1, st') ->
    eval_cfgexpr prog oc st' e2 >>= fun (v2, st'') ->
    let v = eval_binop b v1 v2 in
    OK(v, st'')
  | Eunop(u, e) ->
    eval_cfgexpr prog oc st e >>= fun (v1, st') ->
    let v = (eval_unop u v1) in
    OK(v, st')
  | Eint i -> OK(i, st)
  | Evar s ->
    begin match Hashtbl.find_option st.env s with
      | Some v -> OK(v, st)
      | None -> Error (Printf.sprintf "Unknown variable %s\n" s)
    end
  | Ecall(f, args) -> List.fold_left (fun acc e -> acc >>= fun (l, nst) -> eval_cfgexpr prog oc nst e >>= fun (v, nst') -> OK(l@[v], nst')) (OK([], st)) args >>= fun (args, st') ->
                        match find_function prog f with
                        | OK(fdef) -> eval_cfgfun prog oc st' f fdef args >>= fun (v, st'') -> (
                            match v with
                            | Some v -> OK(v, st'')
                            | None -> Error Printf.(sprintf "CFG: Function %s did not return a value\n" f)
                          )
                        | Error(_) -> do_builtin oc st'.mem f args >>= fun v -> (
                            match v with
                            | Some v -> OK(v, st')
                            | None -> Error Printf.(sprintf "CFG: Function %s did not return a value\n" f)
                          )

and eval_cfginstr prog oc st ht (n: int): (int * int state) res =
  match Hashtbl.find_option ht n with
  | None -> Error (Printf.sprintf "Invalid node identifier\n")
  | Some node ->
    match node with
    | Cnop succ ->
      eval_cfginstr prog oc st ht succ
    | Cassign(v, e, succ) ->
      eval_cfgexpr prog oc st e >>= fun (i, st') ->
      Hashtbl.replace st'.env v i;
      eval_cfginstr prog oc st' ht succ
    | Ccmp(cond, i1, i2) ->
      eval_cfgexpr prog oc st cond >>= fun (i, st') ->
      if i = 0 then eval_cfginstr prog oc st' ht i2 else eval_cfginstr prog oc st' ht i1
    | Creturn(e) ->
      eval_cfgexpr prog oc st e >>= fun (e, st') ->
      OK(e, st')
    | Ccall(f, vargs, succ) -> List.fold_left (fun acc e -> acc >>= fun (l, nst) -> eval_cfgexpr prog oc nst e >>= fun (v, nst') -> OK(l@[v], nst')) (OK([], st)) vargs >>= fun (args, st') ->
                                match find_function prog f with
                                | OK(fdef) -> eval_cfgfun prog oc st' f fdef args >>= fun (_, st'') -> eval_cfginstr prog oc st'' ht succ
                                | Error(_) -> do_builtin oc st'.mem f args >>= fun _ -> eval_cfginstr prog oc st' ht succ
and eval_cfgfun prog oc st cfgfunname { cfgfunargs;
                                      cfgfunbody;
                                      cfgentry} vargs =
  let st' = { st with env = Hashtbl.create 17 } in
  match List.iter2 (fun a v -> Hashtbl.replace st'.env a v) cfgfunargs vargs with
  | () -> eval_cfginstr prog oc st' cfgfunbody cfgentry >>= fun (v, st') ->
    OK (Some v, {st' with env = st.env})
  | exception Invalid_argument _ ->
    Error (Format.sprintf "CFG: Called function %s with %d arguments, expected %d.\n"
             cfgfunname (List.length vargs) (List.length cfgfunargs)
          )

let eval_cfgprog oc cp memsize params =
  let st = init_state memsize in
  find_function cp "main" >>= fun f ->
  let n = List.length f.cfgfunargs in
  let params = take n params in
  eval_cfgfun cp oc st "main" f params >>= fun (v, st) ->
  OK v



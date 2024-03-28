open Batteries
open Elang
open Elang_gen
open Cfg
open Utils
open Prog
open Report
open Cfg_print
open Options

(* [cfg_expr_of_eexpr e] converts an [Elang.expr] into a [expr res]. This should
   always succeed and be straightforward.

   In later versions of this compiler, you will add more things to [Elang.expr]
   but not to [Cfg.expr], hence the distinction.
*)
let rec cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem (e: Elang.expr) : expr res =
  match e with
  | Elang.Ebinop (b, e1, e2) ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e1 >>= fun ee1 ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e2 >>= fun ee2 ->
    (match type_expr typ_struct typ_var typ_fun e1, type_expr typ_struct typ_var typ_fun e2 with
      | OK(Tptr(t1)), OK(Tptr(t2)) -> OK(Ebinop(b, ee1, ee2))
      | OK(Tptr(t1)), _ ->
        size_type typ_struct t1 >>= fun sz -> OK(Ebinop(b, ee1, Ebinop(Emul, ee2, Eint(sz))))
      | _, OK(Tptr(t2)) ->
        size_type typ_struct t2 >>= fun sz -> OK(Ebinop(b, Ebinop(Emul, ee1, Eint(sz)), ee2))
      | _ -> OK(Ebinop(b, ee1, ee2))
    )
  | Elang.Eunop (u, e) ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e >>= fun ee ->
    OK (Eunop (u, ee))
  | Elang.Eint i -> OK(Eint(i))
  | Elang.Echar c -> OK(Eint(int_of_char c))
  | Elang.Evar v ->
      (match Hashtbl.find_option varinmem v with
        | Some(addr) ->
            type_expr typ_struct typ_var typ_fun (Elang.Evar(v)) >>= fun t ->
            size_type typ_struct t >>= fun sz ->
            OK(Eload(Estk(addr), sz))
        | None -> OK(Evar(v))
      )
  | Elang.Ecall(f, el) ->
    List.fold_right (fun e acc ->
        acc >>= fun el ->
        cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e >>= fun e ->
        OK (e::el)
      ) el (OK []) >>= fun el ->
    OK (Ecall (f, el))
  | Elang.Eaddrof(v) -> (match v with
    | Elang.Evar(v) -> (
        match Hashtbl.find_option varinmem v with
        | Some(addr) ->
            OK(Estk(addr))
        | None -> Error("Variable not found")
      )
      | Elang.Eload(e) -> cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e
      | _ -> Error("Invalid expression")
    )
  | Elang.Eload(e) ->
      type_expr typ_struct typ_var typ_fun e >>= fun t ->
      cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e >>= fun v ->
      (match t with
        | Tptr(t') -> size_type typ_struct t' >>= fun sz -> OK(Eload(v, sz))
        | _ -> Error("Invalid type")
      )
  | Elang.Egetfield(e, f) -> (
      match e with
      | Elang.Eaddrof(Elang.Evar(v)) -> (
          match Hashtbl.find_option varinmem v with
          | Some(addr) -> (
              type_expr typ_struct typ_var typ_fun e >>= fun t -> (
                match t with
                | Tptr(Tstruct(s)) -> (
                  match Hashtbl.find_option typ_struct s with
                    | Some(fields) ->
                      field_offset typ_struct s f >>= fun offset ->
                      field_type typ_struct s f >>= fun t ->
                      size_type typ_struct t >>= fun sz ->
                      OK(Eload(Estk(addr + offset), sz))
                    | None -> Error("Struct not found")
                )
                | _ -> Error("Invalid type")
              )
            )
          | None -> Error("Variable not found")
        )
      | _ -> Error("Invalid expression")
    )  

(* [cfg_node_of_einstr next cfg succ i] builds the CFG node(s) that correspond
   to the E instruction [i].

   [cfg] is the current state of the control-flow graph.

   [succ] is the successor of this node in the CFG, i.e. where to go after this
   instruction.

   [next] is the next available CFG node identifier.

   This function returns a pair (n, next) where [n] is the identifer of the
   node generated, and [next] is the new next available CFG node identifier.

   Hint: several nodes may be generated for a single E instruction.
*)
let rec cfg_node_of_einstr typ_struct typ_var typ_fun varinmem (next: int) (cfg : (int, cfg_node) Hashtbl.t)
    (succ: int) (i: instr) : (int * int) res =
  match i with
  | Elang.Iassign (v, e) ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e >>= fun e ->
    (match Hashtbl.find_option varinmem v with
      | Some(addr) ->
        type_expr typ_struct typ_var typ_fun (Elang.Evar(v)) >>= fun t ->
        size_type typ_struct t >>= fun sz ->
        Hashtbl.replace cfg next (Cstore(Estk(addr), e, sz, succ));
        OK (next, next + 1)
      | None ->
        Hashtbl.replace cfg next (Cassign(v, e, succ));
        OK (next, next + 1)
      )    
  | Elang.Iif (c, ithen, ielse) ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem c >>= fun c ->
    cfg_node_of_einstr typ_struct typ_var typ_fun varinmem next cfg succ ithen >>= fun (nthen, next) ->
    cfg_node_of_einstr typ_struct typ_var typ_fun varinmem next cfg succ ielse  >>= fun (nelse, next) ->
    Hashtbl.replace cfg next (Ccmp(c, nthen, nelse)); OK (next, next + 1)
  | Elang.Iwhile (c, i) ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem c >>= fun c ->
    let (cmp, next) = (next, next+1) in
    cfg_node_of_einstr typ_struct typ_var typ_fun varinmem next cfg cmp i >>= fun (nthen, next) ->
    Hashtbl.replace cfg cmp (Ccmp(c, nthen, succ)); OK (cmp, next + 1)
  | Elang.Iblock il ->
    List.fold_right (fun i acc ->
        acc >>= fun (succ, next) ->
        cfg_node_of_einstr typ_struct typ_var typ_fun varinmem next cfg succ i
      ) il (OK (succ, next))
  | Elang.Ireturn e ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e >>= fun e ->
    Hashtbl.replace cfg next (Creturn e); OK (next, next + 1)
  | Elang.Icall(f, el) ->
    List.fold_right (fun e acc ->
        acc >>= fun el ->
        cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e >>= fun e ->
        OK (e::el)
      ) el (OK []) >>= fun el ->
    Hashtbl.replace cfg next (Ccall(f, el, succ));
    OK (next, next + 1)
  | Elang.Istore(e1, e2) ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e1 >>= fun v1 ->
    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem e2 >>= fun v2 ->
    type_expr typ_struct typ_var typ_fun e1 >>= fun t ->
    size_type typ_struct t >>= fun sz ->
    Hashtbl.replace cfg next (Cstore(v1, v2, sz, succ));
    OK (next, next + 1)
  | Elang.Isetfield(e, f, v) -> (
    match e with
    | Elang.Eaddrof(Elang.Evar(var)) -> (
        match Hashtbl.find_option varinmem var with
        | Some(addr) -> (
            type_expr typ_struct typ_var typ_fun e >>= fun t -> (
              match t with
              | Tptr(Tstruct(s)) -> (
                match Hashtbl.find_option typ_struct s with
                  | Some(fields) ->
                    field_offset typ_struct s f >>= fun offset ->
                    field_type typ_struct s f >>= fun t ->
                    size_type typ_struct t >>= fun sz ->
                    cfg_expr_of_eexpr typ_struct typ_var typ_fun varinmem v >>= fun v ->
                    Hashtbl.replace cfg next (Cstore(Estk(addr + offset), v, sz, succ));
                    OK (next, next + 1)
                  | None -> Error("Struct not found")
              )
              | _ -> Error("Invalid type")
            )
          )
        | None -> Error("Variable not found")
      )
    | _ -> Error("Invalid expression")

  )

(* Some nodes may be unreachable after the CFG is entirely generated. The
   [reachable_nodes n cfg] constructs the set of node identifiers that are
   reachable from the entry node [n]. *)
let rec reachable_nodes n (cfg: (int,cfg_node) Hashtbl.t) =
  let rec reachable_aux n reach =
    if Set.mem n reach then reach
    else let reach = Set.add n reach in
      match Hashtbl.find_option cfg n with
      | None -> reach
      | Some (Cnop succ)
      | Some (Cassign (_, _, succ)) -> reachable_aux succ reach
      | Some (Creturn _) -> reach
      | Some (Ccmp (_, s1, s2)) ->
        reachable_aux s1 (reachable_aux s2 reach)
      | Some(Ccall(_, _, succ)) -> reachable_aux succ reach
      | Some(Cstore(_, _, _, succ)) -> reachable_aux succ reach
  in reachable_aux n Set.empty

(* [cfg_fun_of_efun f] builds the CFG for E function [f]. *)
let cfg_fun_of_efun prog typ_fun { funname; funargs; funbody; funvartype; funrettype; funvarinmem; funstksz } =
  let cfg = Hashtbl.create 17 in
  Hashtbl.replace cfg 0 (Creturn (Eint 0));
  Hashtbl.replace typ_fun funname (List.map snd funargs, funrettype);
  cfg_node_of_einstr (snd prog) funvartype typ_fun funvarinmem 1 cfg 0 funbody >>= fun (node, _) ->
  (* remove unreachable nodes *)
  let r = reachable_nodes node cfg in
  Hashtbl.filteri_inplace (fun k _ -> Set.mem k r) cfg;
  OK { cfgfunargs = List.map fst funargs;
       cfgfunbody = cfg;
       cfgentry = node;
       cfgfunstksz = funstksz;
     }

let cfg_gdef_of_edef prog typ_fun gd =
  match gd with
    Gfun f -> cfg_fun_of_efun prog typ_fun f >>= fun f -> OK (Gfun f)

let cfg_prog_of_eprog (ep: eprog) : cfg_fun prog res =
  let typ_fun = Hashtbl.create 17 in
  assoc_map_res (fun _ -> cfg_gdef_of_edef ep typ_fun) (fst ep)

let pass_cfg_gen ep =
  match cfg_prog_of_eprog ep with
  | Error msg ->
    record_compile_result ~error:(Some msg) "CFG"; Error msg
  | OK cfg ->
    record_compile_result "CFG";
    dump !cfg_dump dump_cfg_prog cfg (call_dot "cfg" "CFG");
    OK cfg

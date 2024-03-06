open Ast
open Elang
open Prog
open Report
open Options
open Batteries
open Elang_print
open Utils

let tag_is_binop =
  function
    Tadd -> true
  | Tsub -> true
  | Tmul -> true
  | Tdiv -> true
  | Tmod -> true
  | Txor -> true
  | Tcle -> true
  | Tclt -> true
  | Tcge -> true
  | Tcgt -> true
  | Tceq -> true
  | Tne  -> true
  | _    -> false

let binop_of_tag =
  function
    Tadd -> Eadd
  | Tsub -> Esub
  | Tmul -> Emul
  | Tdiv -> Ediv
  | Tmod -> Emod
  | Txor -> Exor
  | Tcle -> Ecle
  | Tclt -> Eclt
  | Tcge -> Ecge
  | Tcgt -> Ecgt
  | Tceq -> Eceq
  | Tne -> Ecne
  | _ -> assert false

  (* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)
let rec make_eexpr_of_ast (a: tree) : expr res =
  let res =
    match a with
    | Node(t, [e1; e2]) when tag_is_binop t -> 
        make_eexpr_of_ast e1 >>= fun o1 ->
        make_eexpr_of_ast e2 >>= fun o2 -> 
          OK (Ebinop(binop_of_tag t, o1 ,o2))
    |Node(Tneg, [e]) -> make_eexpr_of_ast e >>= fun o -> OK (Eunop(Eneg,o))
    |StringLeaf(s) -> OK (Evar(s))
    |IntLeaf(n) -> OK (Eint(n))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg) 

let rec make_einstr_of_ast (a: tree) : instr res =
  let res =
    match a with
    |Node(Tassign, [Node(Tassignvar,StringLeaf s::[q])]) -> make_eexpr_of_ast q >>= fun q_e -> OK (Iassign (s, q_e))
    |Node(Tif,r::b1::[b2]) -> make_eexpr_of_ast r >>= fun e_r -> make_einstr_of_ast b1 >>= fun b1_i -> make_einstr_of_ast b2 >>= fun b2_i -> OK (Iif (e_r,b1_i,b2_i))
    |Node(Twhile,r::[b]) -> make_eexpr_of_ast r >>= fun e_r -> make_einstr_of_ast b >>= fun b_i -> OK (Iwhile (e_r,b_i))
    |Node(Tblock,list_tree) -> list_map_res make_einstr_of_ast list_tree >>= fun i -> OK (Iblock i)
    |Node(Treturn,[tr]) -> make_eexpr_of_ast tr >>= fun e -> OK (Ireturn e)
    |Node(Tprint,[tr]) -> make_eexpr_of_ast tr >>= fun e -> OK (Iprint e)
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : string res =
  match a with
  | Node (Targ, [s]) ->
    OK (string_of_stringleaf s)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_fundef_of_ast (a: tree) : (string * efun) res =
  match a with
  | Node (Tfundef, [Node(Tfunname, [StringLeaf fname]); Node (Tfunargs, fargs); Node(Tfunbody,[fbody])]) ->
    list_map_res make_ident fargs >>= fun fargs_sl -> 
      make_einstr_of_ast fbody >>= fun fbody_i -> 
      OK (fname, {funargs=fargs_sl;funbody=fbody_i})
  | _ -> Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a))

let make_eprog_of_ast (a: tree) : eprog res =
  match a with
  | Node (Tlistglobdef, l) ->
    list_map_res (fun a -> make_fundef_of_ast a >>= fun (fname, efun) -> OK (fname, Gfun efun)) l
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tlistglobdef, got %s."
             (string_of_ast a))

let pass_elang ast =
  match make_eprog_of_ast ast with
  | Error msg ->
    record_compile_result ~error:(Some msg) "Elang";
    Error msg
  | OK  ep ->
    dump !e_dump dump_e ep (fun file () ->
        add_to_report "e" "E" (Code (file_contents file))); OK ep


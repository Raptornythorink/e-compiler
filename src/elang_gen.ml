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

  let compatible_types t1 t2 =
    if t1 = t2 then true else
    match t1, t2 with
    | Tvoid, _ -> false
    | _, Tvoid -> false
    | _, _ -> true

let rec type_expr (typ_var : (string, typ) Hashtbl.t) (typ_fun : (string, typ list * typ) Hashtbl.t) (e: expr) : typ res =
  match e with
  | Eint(_) -> OK(Tint)
  | Echar(_) -> OK(Tchar)
  | Evar(v) -> 
    if Hashtbl.mem typ_var v then
      OK(Hashtbl.find typ_var v)
    else
      Error(Printf.sprintf "Variable %s not found" v)
  | Ebinop(_, e1, e2) ->
    type_expr typ_var typ_fun e1 >>= fun t1 ->
    type_expr typ_var typ_fun e2 >>= fun t2 ->
    if compatible_types t1 t2 then
      OK(t1)
    else
      Error (Printf.sprintf "Type error in binary operation")
  | Eunop(_, e) ->
    type_expr typ_var typ_fun e
  | Ecall(f, args) ->
    if Hashtbl.mem typ_fun f then
      let (args_typ, ret_typ) = Hashtbl.find typ_fun f in
      if List.length args_typ = List.length args then
        let rec type_args args_typ args =
          match args_typ, args with
          | [], [] -> OK []
          | t::q, a::r -> type_expr typ_var typ_fun a >>= fun ta ->
            if ta = t then
              type_args q r
            else
              Error(Printf.sprintf "Type error while calling function %s: expected %s, got %s" f (string_of_typ t) (string_of_typ ta))
          | _, _ -> assert false
        in
        type_args args_typ args >>= fun _ ->
        OK(ret_typ)
      else
        Error(Printf.sprintf "Wrong number of arguments while calling function %s" f)
    else
      Error(Printf.sprintf "Function %s not found" f)

(* [make_eexpr_of_ast a] builds an expression corresponding to a tree [a]. If
   the tree is not well-formed, fails with an [Error] message. *)
let rec make_eexpr_of_ast typ_var typ_fun (a: tree) : expr res =
  let res =
    match a with
    | IntLeaf(i) -> OK(Eint(i))
    | CharLeaf(c) -> OK(Echar(c))
    | Node(t, [e1; e2]) when tag_is_binop t -> 
      make_eexpr_of_ast typ_var typ_fun e1 >>= fun exp1 ->
      make_eexpr_of_ast typ_var typ_fun e2 >>= fun exp2 ->
      let res = Ebinop(binop_of_tag t, exp1, exp2) in
      type_expr typ_var typ_fun res >>= fun _ -> OK(res)
    | Node(Tneg, [e]) -> 
      make_eexpr_of_ast typ_var typ_fun e >>= fun exp ->
      let res = Eunop(Eneg, exp) in
      type_expr typ_var typ_fun res >>= fun _ -> OK(res)
    | Node(Tint, [IntLeaf(i)]) -> OK(Eint(i))
    | StringLeaf(s) -> OK(Evar(s))
    | Node(Tcall, [Node(Tfunname, [StringLeaf(fname)]); Node(Targs, args)]) ->
      list_map_res (make_eexpr_of_ast typ_var typ_fun) args >>= fun eargs ->
      OK(Ecall(fname, eargs))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_eexpr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_eexpr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let rec make_einstr_of_ast typ_var typ_fun (a: tree) : instr res =
  let res =
    match a with
    | NullLeaf -> OK(Iblock([]))
    | Node(Tassign, [StringLeaf(var); e]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun exp ->
          if Hashtbl.mem typ_var var then
            type_expr typ_var typ_fun exp >>= fun texp ->
            let var_type = Hashtbl.find typ_var var in
            if var_type = Tvoid then
              Error(Printf.sprintf "Cannot assign to void variable %s" var)
            else if compatible_types (Hashtbl.find typ_var var) texp then
              OK(Iassign(var, exp))
            else
              Error(Printf.sprintf "Type error while assigning to variable %s: expected %s, got %s" var (string_of_typ (Hashtbl.find typ_var var)) (string_of_typ texp))
          else
            Error(Printf.sprintf "Variable %s not found" var)
    | Node(Tassign, [Node(Tassignvar, [StringLeaf(var); e])]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun exp ->
          OK(Iassign(var, exp))
    | Node(Tassignvar, [StringLeaf(var); e]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun exp ->
          OK(Iassign(var, exp))
    | Node(Tif, [e; i1; i2]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun exp ->
        make_einstr_of_ast typ_var typ_fun i1 >>= fun instr1 ->
        make_einstr_of_ast typ_var typ_fun i2 >>= fun instr2 ->
          OK(Iif(exp, instr1, instr2))
    | Node(Twhile, [e; i]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun exp ->
        make_einstr_of_ast typ_var typ_fun i >>= fun instr ->
          OK(Iwhile (exp, instr))
    | Node(Tblock, l) ->
        list_map_res (make_einstr_of_ast typ_var typ_fun) l >>= fun instrs ->
          OK(Iblock(instrs))
    | Node(Treturn, [e]) ->
        make_eexpr_of_ast typ_var typ_fun e >>= fun exp ->
          OK(Ireturn(exp))
    | Node(Tcall, [Node(Tfunname, [StringLeaf(fname)]); Node(Targs, args)]) ->
        list_map_res (make_eexpr_of_ast typ_var typ_fun) args >>= fun eargs ->
          OK(Icall(fname, eargs))
    | Node(Tvardef, [StringLeaf("int"); StringLeaf(vname); NullLeaf]) -> 
        Hashtbl.replace typ_var vname Tint;
          OK(Iblock([]))
    | Node(Tvardef, [StringLeaf("char"); StringLeaf(vname); NullLeaf]) ->
        Hashtbl.replace typ_var vname Tchar;
          OK(Iblock([]))
    | Node(Tvardef, [StringLeaf("void"); StringLeaf(vname); NullLeaf]) ->
        Error(Printf.sprintf "Cannot declare variable %s of type void" vname)
    | Node(Tvardef, [StringLeaf("int"); StringLeaf(vname); Node(Tassignvar,[a'])])->
        Hashtbl.replace typ_var vname Tint;
        make_eexpr_of_ast typ_var typ_fun a' >>= fun i ->
          if compatible_types (Hashtbl.find typ_var vname) Tint then
            OK(Iassign(vname, i))
          else
            Error(Printf.sprintf "Type error while assigning to variable %s: expected %s, got %s" vname (string_of_typ (Hashtbl.find typ_var vname)) (string_of_typ Tint))
    | Node(Tvardef, [StringLeaf("char"); StringLeaf(vname); Node(Tassignvar, [a'])]) ->
        Hashtbl.replace typ_var vname Tchar;
        make_eexpr_of_ast typ_var typ_fun a' >>= fun i ->
          if compatible_types (Hashtbl.find typ_var vname) Tchar then
            OK(Iassign(vname, i))
          else
            Error(Printf.sprintf "Type error while assigning to variable %s: expected %s, got %s" vname (string_of_typ (Hashtbl.find typ_var vname)) (string_of_typ Tchar))
    | _ -> Error (Printf.sprintf "Unacceptable ast in make_einstr_of_ast %s"
                    (string_of_ast a))
  in
  match res with
    OK o -> res
  | Error msg -> Error (Format.sprintf "In make_einstr_of_ast %s:\n%s"
                          (string_of_ast a) msg)

let make_ident (a: tree) : (string * typ) res =
  match a with
  | Node (Targ, [StringLeaf("int"); s]) ->
    OK(string_of_stringleaf s, Tint)
  | Node (Targ, [StringLeaf("char"); s]) ->
    OK(string_of_stringleaf s, Tchar)
  | a -> Error (Printf.sprintf "make_ident: unexpected AST: %s"
                  (string_of_ast a))

let make_fundef_of_ast typ_fun (a: tree) : (string * efun) res =
  match a with
  | Node (Tfundef, [Node(Tfunrettype, [StringLeaf(rettype)]); Node(Tfunname, [StringLeaf(fname)]); Node (Tfunargs, fargs); Node(Tfunbody, [fbody])]) ->
    list_map_res make_ident fargs >>= fun funargs ->
    let typ_var = Hashtbl.create 17 in
    List.iter (fun (s, t) -> Hashtbl.replace typ_var s t) funargs;
    typ_of_string rettype >>= fun funrettype ->
    let argstype = List.map snd funargs in
    Hashtbl.replace typ_fun fname (argstype, funrettype);
    make_einstr_of_ast typ_var typ_fun fbody >>= fun funbody ->
     OK((fname, { funargs = funargs; funbody = funbody; funvartype = typ_var; funrettype = funrettype }))
  | _ ->
    Error (Printf.sprintf "make_fundef_of_ast: Expected a Tfundef, got %s."
             (string_of_ast a))

let make_eprog_of_ast (a: tree) : eprog res =
  let fun_typ = Hashtbl.create 17 in
  Hashtbl.replace fun_typ "print" ([Tint], Tvoid);
  Hashtbl.replace fun_typ "print_int" ([Tint], Tvoid);
  Hashtbl.replace fun_typ "print_char" ([Tchar], Tvoid);
  match a with
  | Node (Tlistglobdef, l) ->
    let prog = list_map_res (fun a -> make_fundef_of_ast fun_typ a >>= fun (fname, efun) -> OK (fname, Gfun efun)) l in
    (match prog with 
    | OK(funlist) ->
      let seen = Hashtbl.create (List.length funlist) in
      OK(
        List.fold_left (
          fun acc (fname, gfun) ->
            if Hashtbl.mem seen fname then acc
            else begin
              Hashtbl.add seen fname ();
              (fname, gfun)::acc
            end
        ) [] (List.rev funlist)
      )
    | Error(msg) -> Error(msg)
    )
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


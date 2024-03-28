open Batteries
open Utils

type mem_access_size =
  | MAS1
  | MAS4
  | MAS8

let string_of_mem_access_size mas =
  match mas with
  | MAS1 -> "{1}"
  | MAS4 -> "{4}"
  | MAS8 -> "{8}"

let mas_of_size n =
  match n with
  | 1 -> OK MAS1
  | 4 -> OK MAS4
  | 8 -> OK MAS8
  | _ -> Error (Printf.sprintf "Unknown memory access size for size = %d" n)


let size_of_mas mas =
  match mas with
  | MAS1 -> 1
  | MAS4 -> 4
  | MAS8 -> 8

let archi_mas () =
  match !Archi.archi with
  | A64 -> MAS8
  | A32 -> MAS4


type 'a gdef = Gfun of 'a

type 'a prog = (string * 'a gdef) list


let dump_gdef dump_fun oc gd =
  match gd with
  | (fname, Gfun f) ->
    dump_fun oc fname f;
    Format.fprintf oc "\n"

let dump_prog dump_fun oc =
  List.iter (dump_gdef dump_fun oc)

type 'a state = {
  env: (string, 'a) Hashtbl.t;
  mem: Mem.t
}

let init_state memsize =
  {
    mem = Mem.init memsize;
    env = Hashtbl.create 17;
  }

let set_val env v i =
  Hashtbl.replace env v i

let get_val env v =
  Hashtbl.find_option env v

let find_function (ep: 'a prog) fname : 'a res =
  match List.assoc_opt fname ep with
  | Some (Gfun f) -> OK f
  | _ -> Error (Format.sprintf "Unknown function %s\n" fname)

type typ =
  | Tint
  | Tchar
  | Tvoid
  | Tptr of typ
  | Tstruct of string

let rec string_of_typ t =
  match t with
  | Tint -> "int"
  | Tchar -> "char"
  | Tvoid -> "void"
  | Tptr t' -> Printf.sprintf "%s*" (string_of_typ t')
  | Tstruct(structname) -> Printf.sprintf "struct %s" structname

let rec typ_of_string s =
  match s with
  | "int" -> OK Tint
  | "char" -> OK Tchar
  | "void" -> OK Tvoid
  | "*" -> Error "Cannot parse type * without a base type"
  | s when String.ends_with s "*" -> typ_of_string (String.sub s 0 (String.length s - 1)) >>= fun t -> OK (Tptr t)
  | s when String.starts_with s "struct " -> OK (Tstruct (String.sub s 7 (String.length s - 7)))
  | _ -> Error (Printf.sprintf "Unknown type %s" s)

let rec size_type (structs: (string, (string * typ) list) Hashtbl.t) (t: typ) : int res =
  match t with
  | Tint -> OK(8)
  | Tchar -> OK(1)
  | Tvoid -> Error "Cannot get size of void type"
  | Tptr _ -> OK(8)
  | Tstruct(structname) ->
    match Hashtbl.find_option structs structname with
    | Some fields ->
      List.fold_left (fun acc (_, t) -> acc >>= fun acc -> size_type structs t >>= fun size -> OK (acc + size)) (OK 0) fields
    | None -> Error (Printf.sprintf "Unknown struct %s" structname)

let field_offset (structs: (string, (string * typ) list) Hashtbl.t) (s: string) (f: string) : int res =
  match Hashtbl.find_option structs s with
  | Some fields ->
    let rec aux acc = function
      | [] -> Error (Printf.sprintf "Unknown field %s in struct %s" f s)
      | (fname, t) :: tl when fname = f -> OK acc
      | (_, t) :: tl -> size_type structs t >>= fun size -> aux (acc + size) tl
    in
    aux 0 fields
  | None -> Error (Printf.sprintf "Unknown struct %s" s)

let field_type (structs: (string, (string * typ) list) Hashtbl.t) (s: string) (f: string) : typ res =
  match Hashtbl.find_option structs s with
  | Some fields ->
    let rec aux = function
      | [] -> Error (Printf.sprintf "Unknown field %s in struct %s" f s)
      | (fname, t) :: tl when fname = f -> OK t
      | _ :: tl -> aux tl
    in
    aux fields
  | None -> Error (Printf.sprintf "Unknown struct %s" s)

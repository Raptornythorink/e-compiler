tokens SYM_EOF SYM_IDENTIFIER<string> SYM_INTEGER<int> SYM_CHARACTER<char> SYM_PLUS SYM_MINUS SYM_ASTERISK SYM_DIV SYM_MOD SYM_AMPERSAND SYM_POINT
tokens SYM_LPARENTHESIS SYM_RPARENTHESIS SYM_LBRACE SYM_RBRACE
tokens SYM_ASSIGN SYM_SEMICOLON SYM_RETURN SYM_IF SYM_WHILE SYM_ELSE SYM_COMMA
tokens SYM_EQUALITY SYM_NOTEQ SYM_LT SYM_LEQ SYM_GT SYM_GEQ
tokens SYM_INT SYM_CHAR SYM_VOID SYM_STRUCT
non-terminals S INSTR<tree> INSTRS<tree list> LINSTRS ELSE EXPR FACTOR
non-terminals LPARAMS REST_PARAMS CALL_PARAMS REST_CALL_PARAMS PARAM_DEF
non-terminals IDENTIFIER INTEGER CHAR
non-terminals GLOBDEF GLOBDEFS FUNDEF REST_FUNDEF FUNDEFS STRUCTDEF STRUCTDEFS
non-terminals VARDEF FIELDDEF FIELDDEFS
non-terminals ADD_EXPRS ADD_EXPR
non-terminals MUL_EXPRS MUL_EXPR
non-terminals CMP_EXPRS CMP_EXPR
non-terminals EQ_EXPRS EQ_EXPR
non-terminals ID_INSTR ID_EXPR
non-terminals BASE_TYPE TYPE PTR_TYPE
axiom S
{

  open Symbols
  open Ast
  open BatPrintf
  open BatBuffer
  open Batteries
  open Utils

  let rec resolve_associativity term other =
       match other with
       | [] -> term
       | (op, operand)::other' -> resolve_associativity (Node (op, [term; operand])) other'

}

rules
S -> GLOBDEFS SYM_EOF { Node (Tlistglobdef, $1) }
GLOBDEFS -> GLOBDEF GLOBDEFS { $1::$2 }
GLOBDEFS -> { [] }
GLOBDEF -> FUNDEF { $1 }
GLOBDEF -> STRUCTDEF { $1 }
BASE_TYPE -> SYM_INT { StringLeaf "int" }
BASE_TYPE -> SYM_CHAR { StringLeaf "char" }
BASE_TYPE -> SYM_VOID { StringLeaf "void" }
TYPE -> BASE_TYPE PTR_TYPE { $2 $1 }
PTR_TYPE -> SYM_ASTERISK PTR_TYPE { fun leaf -> $2 (StringLeaf((string_of_stringleaf leaf)^"*")) }
PTR_TYPE -> { fun leaf -> StringLeaf((string_of_stringleaf leaf)) }
FUNDEFS -> FUNDEF FUNDEFS { $1::$2 }
FUNDEFS -> { [] }
FUNDEF -> TYPE IDENTIFIER SYM_LPARENTHESIS LPARAMS SYM_RPARENTHESIS REST_FUNDEF { Node (Tfundef, [Node(Tfunrettype, [$1]); Node(Tfunname, [$2]); Node(Tfunargs, $4); Node(Tfunbody, [$6]);]) }
REST_FUNDEF -> SYM_SEMICOLON { NullLeaf }
REST_FUNDEF -> INSTR { $1 }
STRUCTDEFS -> STRUCTDEF STRUCTDEFS { $1::$2 }
STRUCTDEFS -> { [] }
STRUCTDEF -> SYM_STRUCT IDENTIFIER SYM_LBRACE FIELDDEFS SYM_RBRACE SYM_SEMICOLON { Node (Tstructdef, [Node(Tstructname, [$2]); Node(Tstructfields, $4)]) }
FIELDDEFS -> FIELDDEF FIELDDEFS { $1::$2 }
FIELDDEFS -> { [] }
FIELDDEF -> TYPE IDENTIFIER SYM_SEMICOLON { Node (Tfielddef, [$1; $2]) }
FIELDDEF -> SYM_STRUCT IDENTIFIER IDENTIFIER SYM_SEMICOLON { Node (Tfielddef, [StringLeaf("struct " ^ (string_of_stringleaf $2)); $3]) }
LPARAMS -> TYPE IDENTIFIER REST_PARAMS { (Node(Targ, [$1; $2]))::$3 }
LPARAMS -> SYM_STRUCT IDENTIFIER IDENTIFIER REST_PARAMS { (Node(Targ, [StringLeaf("struct " ^ (string_of_stringleaf $2)); $3]))::$4 }
LPARAMS -> { [] }
REST_PARAMS -> SYM_COMMA PARAM_DEF REST_PARAMS { $2::$3 }
REST_PARAMS -> { [] }
PARAM_DEF -> TYPE IDENTIFIER { Node(Targ, [$1; $2]) }
PARAM_DEF -> SYM_STRUCT IDENTIFIER IDENTIFIER { Node(Targ, [StringLeaf("struct " ^ (string_of_stringleaf $2)); $3]) }
CALL_PARAMS -> EXPR REST_CALL_PARAMS { $1::$2 }
CALL_PARAMS -> { [] }
REST_CALL_PARAMS -> SYM_COMMA EXPR REST_CALL_PARAMS { $2::$3 }
REST_CALL_PARAMS -> { [] }
IDENTIFIER -> SYM_IDENTIFIER { StringLeaf $1 }
INTEGER -> SYM_INTEGER { IntLeaf $1 }
CHAR -> SYM_CHARACTER { CharLeaf $1 }
LINSTRS -> SYM_LBRACE INSTRS SYM_RBRACE { Node(Tblock, $2) }
INSTRS -> INSTR INSTRS { $1::$2 }
INSTRS -> { [] }
INSTR -> LINSTRS { $1 }
INSTR -> IDENTIFIER ID_INSTR { $2 $1 }
INSTR -> SYM_IF SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS LINSTRS ELSE { Node(Tif, [$3; $5; $6]) }
INSTR -> SYM_WHILE SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS INSTR { Node(Twhile, [$3; $5]) }
INSTR -> SYM_RETURN EXPR SYM_SEMICOLON { Node(Treturn, [$2]) }
INSTR -> TYPE IDENTIFIER VARDEF SYM_SEMICOLON { Node(Tvardef, [$1; $2; $3]) }
INSTR -> SYM_ASTERISK EXPR SYM_ASSIGN EXPR SYM_SEMICOLON { Node(Tstore, [$2; $4]) }
INSTR -> SYM_STRUCT IDENTIFIER IDENTIFIER SYM_SEMICOLON { Node(Tvardef, [StringLeaf("struct " ^ (string_of_stringleaf $2)); $3; NullLeaf]) }
VARDEF -> SYM_ASSIGN EXPR { Node(Tassignvar, [$2]) }
VARDEF -> { NullLeaf }
ID_INSTR -> SYM_LPARENTHESIS CALL_PARAMS SYM_RPARENTHESIS SYM_SEMICOLON { fun id -> Node(Tcall, [Node(Tfunname, [id]); Node(Targs, $2)]) }
ID_INSTR -> SYM_ASSIGN EXPR SYM_SEMICOLON { fun id -> Node(Tassign, [Node(Tassignvar, [id; $2])]) }
ID_INSTR -> SYM_POINT IDENTIFIER SYM_ASSIGN EXPR SYM_SEMICOLON { fun id -> Node(Tsetfield, [id; $2; $4]) }
ID_INSTR -> SYM_SEMICOLON { fun id -> Node(Tassignvar, []) }
ELSE -> SYM_ELSE LINSTRS { $2 }
ELSE -> { NullLeaf}
EXPR -> CMP_EXPR CMP_EXPRS { resolve_associativity $1 $2 }
CMP_EXPRS -> SYM_LT CMP_EXPR CMP_EXPRS { (Tclt, $2)::$3 }
CMP_EXPRS -> SYM_LEQ CMP_EXPR CMP_EXPRS { (Tcle, $2)::$3 }
CMP_EXPRS -> SYM_GT CMP_EXPR CMP_EXPRS { (Tcgt, $2)::$3 }
CMP_EXPRS -> SYM_GEQ CMP_EXPR CMP_EXPRS { (Tcge, $2)::$3 }
CMP_EXPRS -> { [] }
CMP_EXPR -> EQ_EXPR EQ_EXPRS { resolve_associativity $1 $2 }
EQ_EXPRS -> SYM_EQUALITY EQ_EXPR EQ_EXPRS { (Tceq, $2)::$3 }
EQ_EXPRS -> SYM_NOTEQ EQ_EXPR EQ_EXPRS { (Tne, $2)::$3 }
EQ_EXPRS -> { [] }
EQ_EXPR -> ADD_EXPR ADD_EXPRS { resolve_associativity $1 $2 }
ADD_EXPRS -> SYM_PLUS ADD_EXPR ADD_EXPRS { (Tadd, $2)::$3 }
ADD_EXPRS -> SYM_MINUS ADD_EXPR ADD_EXPRS { (Tsub, $2)::$3 }
ADD_EXPRS -> { [] }
ADD_EXPR -> MUL_EXPR MUL_EXPRS { resolve_associativity $1 $2 }
MUL_EXPRS -> SYM_ASTERISK MUL_EXPR MUL_EXPRS { (Tmul, $2)::$3 }
MUL_EXPRS -> SYM_DIV MUL_EXPR MUL_EXPRS { (Tdiv, $2)::$3 }
MUL_EXPRS -> SYM_MOD MUL_EXPR MUL_EXPRS { (Tmod, $2)::$3 }
MUL_EXPRS -> { [] }
MUL_EXPR -> FACTOR { $1 }
FACTOR -> IDENTIFIER ID_EXPR { $2 $1 }
FACTOR -> INTEGER { Node(Tint, [$1]) }
FACTOR -> CHAR { $1 }
FACTOR -> SYM_LPARENTHESIS EXPR SYM_RPARENTHESIS { $2 }
FACTOR -> SYM_MINUS FACTOR { Node (Tneg, [$2]) }
FACTOR -> SYM_ASTERISK FACTOR { Node (Tload, [$2]) }
FACTOR -> SYM_AMPERSAND FACTOR { Node (Taddrof, [$2]) }
ID_EXPR -> SYM_LPARENTHESIS CALL_PARAMS SYM_RPARENTHESIS { fun id -> Node(Tcall, [Node(Tfunname, [id]); Node(Targs, $2)]) }
ID_EXPR -> SYM_POINT FACTOR { fun id -> Node(Tgetfield, [id; $2]) }
ID_EXPR -> { fun id -> id }

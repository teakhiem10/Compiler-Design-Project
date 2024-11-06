%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF
%token <int64>  INT
%token <bool>   BOOL
%token NULL
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TBOOL    /* bool */
%token TVOID    /* void */
%token TSTRING  /* string */
%token IF       /* if */
%token ELSE     /* else */
%token FOR      /* for */
%token WHILE    /* while */
%token RETURN   /* return */
%token VAR      /* var */
%token NEW      /* new */

%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */
%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token SHLT     /*<<*/
%token SHRL     /*>>*/
%token SHRA     /*>>>*/
%token LT       /* < */
%token LTEQ     /* <= */
%token GT       /* > */
%token GTEQ     /* >= */
%token EQEQ     /* == */
%token EQ       /* = */
%token NEQ      /* != */
%token AND    /* & */
%token OR     /* | */
%token BITAND   /* [&] */
%token BITOR    /* [|]*/
%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */
%token TILDE    /* ~ */
%token BANG     /* ! */
%token GLOBAL   /* global */

%left BITOR
%left BITAND
%left OR
%left AND
%left EQEQ NEQ
%left LT LTEQ GT GTEQ
%left SHLT SHRA SHRL
%left PLUS DASH
%left STAR
%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
%nonassoc LPAREN

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

prog:
  | p=list(decl) EOF  { p }

decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }
    
ty:
  | TINT   { TInt }
  | r=rtyp { TRef r } 
  | TBOOL  { TBool}

%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

%inline bop:
  | PLUS   { Add }
  | DASH   { Sub }
  | STAR   { Mul }
  | SHLT   { Shl }
  | SHRL   { Shr }
  | SHRA   { Sar }
  | LT     { Lt  }
  | LTEQ   { Lte }
  | GT     { Gt }
  | GTEQ   { Gte }
  | EQEQ   { Eq }
  | NEQ    { Neq }
  | AND    { And }
  | OR     { Or }
  | BITAND { IAnd } 
  | BITOR  { IOr }

%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

%inline array_decl:
  | NEW t=ty LBRACKET { t }

gexp:
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | s=STRING            { loc $startpos $endpos @@ CStr s}
  | t=rtyp NULL         { loc $startpos $endpos @@ CNull t }
  | b=BOOL              { loc $startpos $endpos @@ CBool b }
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, gexp) RBRACE
                        { loc $startpos $endpos @@ CArr (t, es) }

lhs:  
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

exp:
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | b=BOOL              { loc $startpos $endpos @@ CBool b }
  | s=STRING            { loc $startpos $endpos @@ CStr s }
  | t=rtyp NULL         { loc $startpos $endpos @@ CNull t }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e,es) }
  //    t=btyp does not work, results in conflicts
  | NEW t=ty LBRACKET e=exp RBRACKET 
                        { 
                          match t with 
                          | TInt | TBool -> loc $startpos $endpos @@ NewArr (t, e)
                          | _ -> failwith "Only basic types allowed"  
                        } (* This feels really wrong to put here *)
  | NEW t=ty LBRACKET RBRACKET LBRACE es=separated_list(COMMA, exp) RBRACE 
                        { loc $startpos $endpos @@ CArr (t, es) }
  | LPAREN e=exp RPAREN { e } 

vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

stmt: 
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | f=for_stmt        { f }
  | WHILE LPAREN e=exp RPAREN b=block  
                        { loc $startpos $endpos @@ While(e, b) }

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }

for_stmt:
  | FOR LPAREN v=separated_list(COMMA,vdecl) SEMI e=exp SEMI st=stmt RPAREN b=block {loc $startpos $endpos @@ For (v, Some e,Some st,b)}
  | FOR LPAREN v=separated_list(COMMA,vdecl) SEMI       SEMI st=stmt RPAREN b=block {loc $startpos $endpos @@ For (v, None, Some st, b)}
  | FOR LPAREN v=separated_list(COMMA,vdecl) SEMI e=exp SEMI         RPAREN b=block {loc $startpos $endpos @@ For (v,Some e, None, b)}
  | FOR LPAREN v=separated_list(COMMA,vdecl) SEMI       SEMI         RPAREN b=block {loc $startpos $endpos @@ For (v,None,None,b)}
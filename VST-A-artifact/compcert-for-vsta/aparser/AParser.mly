%{
exception RepeatedArgument

let unique_idents pl =
  let sorted = List.sort_uniq compare pl in
    if List.length sorted = List.length pl
    then pl
    else raise RepeatedArgument

let process_exgiven exs a givens =
  let exs = unique_idents exs in
  let givens = unique_idents givens in
    if List.for_all (fun id -> List.mem id exs) givens then
      let rest_exs = List.filter (fun id -> not (List.mem id givens)) exs in
      let a = Aabs.EXISTS (rest_exs, a) in
        AClight.Assertion_exgiven (a, givens)
    else
      failwith "given unknown variables"
%}

%token <int> CONSTANT
%token <string> IDENT
%token PLUS MINUS STAR SLASH PERCENT
%token ADDADD COLONCOLON
%token LPAREN RPAREN LBRACE RBRACE COMMA
%token ANDAND NOT DASHSTAR
%token EQEQ NOTEQ GTEQ LTEQ GT LT
%token FORALL EXISTS
%token WITH REQUIRE ENSURE ASSERT GIVEN INVARIANT
%token EOA

%nonassoc QUANTIFICATION
%left ANDAND
%nonassoc EQEQ NOTEQ GTEQ LTEQ GT LT
%right ADDADD
%right COLONCOLON
%left PLUS MINUS
%left STAR SLASH PERCENT
%nonassoc DASHSTAR
%nonassoc NOT

%start <(string, Aabs.expression) AClight.user_assertion> parse_assertion

%type <Aabs.expression> expression
%type <Aabs.expression> expression1

%type <Aabs.expression list> argument_expression_list
%type <string list> ident_list

%%
parse_assertion:
| REQUIRE pre = expression ENSURE post = expression EOA
    { AClight.Funcspec ([], pre, post) }
| WITH frees = ident_list REQUIRE pre = expression ENSURE post = expression EOA
    { AClight.Funcspec (unique_idents frees, pre, post) }
| ASSERT asrt = expression EOA
    { AClight.Assertion asrt }
| ASSERT EXISTS exs = ident_list COMMA asrt = expression GIVEN givens = ident_list EOA
    { process_exgiven exs asrt givens }
| INVARIANT asrt = expression EOA
    { AClight.Invariant asrt }

%inline relation_operator:
| EQEQ  { Aabs.EQ }
| NOTEQ { Aabs.NE }
| GTEQ  { Aabs.GE }
| LTEQ  { Aabs.LE }
| GT    { Aabs.GT }
| LT    { Aabs.LT }

expression:
| FORALL vars = ident_list COMMA expr = expression
    { Aabs.FORALL (unique_idents vars, expr) } %prec QUANTIFICATION
| EXISTS vars = ident_list COMMA expr = expression
    { Aabs.EXISTS (unique_idents vars, expr) } %prec QUANTIFICATION
| expr1 = expression ANDAND expr2 = expression
    { Aabs.BINARY (Aabs.AND, expr1, expr2) }
| expr1 = expression op = relation_operator expr2 = expression
    { Aabs.RELATION (op, expr1, expr2) }
| expr1 = expression PLUS expr2 = expression
    { Aabs.BINARY (Aabs.ADD, expr1, expr2) }
| expr1 = expression MINUS expr2 = expression
    { Aabs.BINARY (Aabs.SUB, expr1, expr2) }
| expr1 = expression STAR expr2 = expression
    { Aabs.BINARY (Aabs.MUL, expr1, expr2) }
| expr1 = expression SLASH expr2 = expression
    { Aabs.BINARY (Aabs.DIV, expr1, expr2) }
| expr1 = expression PERCENT expr2 = expression
    { Aabs.BINARY (Aabs.MOD, expr1, expr2) }
| expr1 = expression DASHSTAR expr2 = expression
    { Aabs.BINARY (Aabs.SEPIMP, expr1, expr2) }
| expr1 = expression ADDADD expr2 = expression
    { Aabs.BINARY (Aabs.APPEND, expr1, expr2) }
| expr1 = expression COLONCOLON expr2 = expression
    { Aabs.BINARY (Aabs.CONS, expr1, expr2) }
| expr = expression1
    { expr }

expression1:
| NOT expr = expression1
    { Aabs.UNARY (Aabs.NOT, expr) }
| MINUS expr = expression1
    { Aabs.UNARY (Aabs.MINUS, expr) }
| func = IDENT LPAREN args = argument_expression_list RPAREN
    { Aabs.FUNCAPP (func, args) }
| var = IDENT
    { Aabs.VARIABLE var }
| cst = CONSTANT
    { Aabs.CONSTANT cst }
| LBRACE args = argument_expression_list RBRACE
    { Aabs.TUPLE args }
| LPAREN expr = expression RPAREN
    { expr }

argument_expression_list:
| exprq = expression COMMA exprt = argument_expression_list
    { (exprq :: exprt) }
| expr = expression
    { [expr] }
|   { [] }

ident_list:
| identq = IDENT identt = ident_list
    { (identq :: identt) }
| ident = IDENT
    { [ident] }

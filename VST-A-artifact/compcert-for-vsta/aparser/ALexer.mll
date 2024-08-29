{
}

let ident_start = ['a'-'z' 'A'-'Z' '_']
let ident_cont = ['a'-'z' 'A'-'Z' '_' '0'-'9']
let digit = ['0'-'9']
let whitespace = [' ' '\t' '\r' '\n']

rule tokenize = parse
  | eof                            { AParser.EOA }
  | "+"                            { AParser.PLUS }
  | "-"                            { AParser.MINUS }
  | "*"                            { AParser.STAR }
  | '/'                            { AParser.SLASH }
  | '%'                            { AParser.PERCENT }
  | "::"                           { AParser.COLONCOLON }
  | "++"                           { AParser.ADDADD }
  | "("                            { AParser.LPAREN }
  | ")"                            { AParser.RPAREN }
  | '{'                            { AParser.LBRACE }
  | '}'                            { AParser.RBRACE }
  | ","                            { AParser.COMMA }
  | "&&"                           { AParser.ANDAND }
  | "-*"                           { AParser.DASHSTAR }
  | "!"                            { AParser.NOT }
  | "=="                           { AParser.EQEQ }
  | "!="                           { AParser.NOTEQ }
  | ">="                           { AParser.GTEQ }
  | "<="                           { AParser.LTEQ }
  | ">"                            { AParser.GT }
  | "<"                            { AParser.LT }
  | "forall"                       { AParser.FORALL }
  | "exists"                       { AParser.EXISTS }
  | "With"                         { AParser.WITH }
  | "Require"                      { AParser.REQUIRE }
  | "Ensure"                       { AParser.ENSURE }
  | "Assert"                       { AParser.ASSERT }
  | "Given"                        { AParser.GIVEN }
  | "Inv"                          { AParser.INVARIANT }
  | (digit+) as num                { AParser.CONSTANT (int_of_string num) }
  | (ident_start ident_cont*) as s { AParser.IDENT s }
  | whitespace+                    { tokenize lexbuf }

{
}

let lex_start_trace = ref []

let trace_tokenize lexbuf =
  let startp = Lexing.lexeme_start lexbuf in
  lex_start_trace := startp :: !lex_start_trace;
  ALexer.tokenize lexbuf

exception Assertion_syntax_error_in of string

let map_user_a f =
  let open AClight in
  function
  | Funcspec (vars, pre, post) -> Funcspec (vars, f pre, f post)
  | Assertion a -> Assertion (f a)
  | Assertion_exgiven (a, vars) -> Assertion_exgiven (f a, vars)
  | Invariant a -> Invariant (f a)

let parse_assertion s =
  lex_start_trace := [];
  let lexbuf = Lexing.from_string s in
  (try AParser.parse_assertion trace_tokenize lexbuf
   with AParser.Error ->
     let endp = Lexing.lexeme_end lexbuf in
     let startp =
       match !lex_start_trace with [] -> 0 | [ p ] -> p | _ :: p :: _ -> p
     in
     let context =
       Bytes.sub_string lexbuf.Lexing.lex_buffer startp (endp - startp)
     in
     raise (Assertion_syntax_error_in context))
  |> map_user_a AAst.Gen.gen_assertion

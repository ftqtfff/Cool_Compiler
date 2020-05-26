{ 
let line_number = ref 1
let commentFlag = ref 0 (*0 indicates outside comment section; 1 indicates inside comment section; 2 indicates single line comment*)
type token =            (*list token names*)
 | Integer of int
 | String of string
 | Plus
 | Minus
 | Times
 | At
 | Case
 | Esac
 | Class
 | Colon
 | Comma
 | Divide
 | Dot
 | Else
 | Equals
 | False
 | If
 | Fi
 | Then
 | Identifier of string
 | Type of string
 | In
 | Inherits
 | Isvoid
 | Larrow
 | Rarrow
 | Lbrace
 | Rbrace
 | Lparen
 | Rparen
 | Le
 | Let
 | Loop
 | Pool
 | Lt
 | New
 | Not
 | Of
 | Semi
 | Tilde 
 | True
 | While

exception Eof (*End of File*)
exception SingleRcomment  (*Only the right parenthese of comment is shown in the src code*)
}

rule token = parse  (*Do lexing*)
| [' ' '\t']  {token lexbuf}  (*If the input character is a white space, we skip it and continue lexing*) 
| '(' '*'           { if !commentFlag = 0 then commentFlag:=1; token lexbuf }
| '*' ')'           { if !commentFlag = 1 then begin commentFlag:=0 ; token lexbuf end else raise SingleRcomment}
| ['\n'] {incr line_number; if !commentFlag = 2 then commentFlag:=0 ; token lexbuf }
| '\"' [^'\"']* '\"' as lxs {!line_number, !commentFlag, String(lxs) }
| '+'               {!line_number, !commentFlag, Plus }
| '-'               {!line_number, !commentFlag, Minus}
| '-' '-'           {commentFlag:=2; token lexbuf }
| '*'               {!line_number, !commentFlag, Times}
| '='               {!line_number, !commentFlag, Equals}
| '/'               {!line_number, !commentFlag, Divide}
| '@'               {!line_number, !commentFlag, At}
| "case"          {!line_number, !commentFlag, Case}
| "esac"          {!line_number, !commentFlag, Esac} 
| "class"         {!line_number, !commentFlag, Class}
| ':'               {!line_number, !commentFlag, Colon}
| ','               {!line_number, !commentFlag, Comma}
| '.'               {!line_number, !commentFlag, Dot}
| "else"          {!line_number, !commentFlag, Else}
| "false"         {!line_number, !commentFlag, False}
| "true"          {!line_number, !commentFlag, True}
| "if"            {!line_number, !commentFlag, If}
| "fi"            {!line_number, !commentFlag, Fi}
| "then"          {!line_number, !commentFlag, Then}
| "in"            {!line_number, !commentFlag, In}
| "inherits"      {!line_number, !commentFlag, Inherits}
| "isvoid"        {!line_number, !commentFlag, Isvoid}
| '<' '-'           {!line_number, !commentFlag, Larrow}
| '=' '>'           {!line_number, !commentFlag, Rarrow} 
| '{'               {!line_number, !commentFlag, Lbrace}
| '}'               {!line_number, !commentFlag, Rbrace}
| '('               {!line_number, !commentFlag, Lparen}        
| ')'               {!line_number, !commentFlag, Rparen}
| '<' '='           {!line_number, !commentFlag, Le} 
| '<'               {!line_number, !commentFlag, Lt} 
| "let"           {!line_number, !commentFlag, Let} 
| "loop"          {!line_number, !commentFlag, Loop}
| "pool"          {!line_number, !commentFlag, Pool}
| "new"           {!line_number, !commentFlag, New}
| "not"             {!line_number, !commentFlag, Not}
| "of"            {!line_number, !commentFlag, Of}
| ';'               {!line_number, !commentFlag, Semi}
| '~'               {!line_number, !commentFlag, Tilde}
| "while"         {!line_number, !commentFlag, While}
| ['a'-'z'] ['_' 'A'-'Z' 'a'-'z' '0'-'9']* as lxs {!line_number, !commentFlag, Identifier(lxs) }
| ['A'-'Z'] ['_' 'A'-'Z' 'a'-'z' '0'-'9']* as lxs {!line_number, !commentFlag, Type(lxs) }
| ['0'-'9']+ as lxm {!line_number, !commentFlag, Integer(int_of_string lxm) }
| eof               {raise Eof}

{
let main() = begin
  let outbuf = Buffer.create 255 in
  let filename = Sys.argv.(1) in
  let file_handle = open_in filename in
  let lexbuf = Lexing.from_channel file_handle in   (*read from a .cl file*)
  try 
         while true do
           let line, flag, result = token lexbuf in    
              if flag = 0 then begin  (*If there is no comment, we print the output to outbuf*)
		   Printf.bprintf outbuf "%d\n" line;
		   match result with
                   | Integer(i) -> Printf.bprintf outbuf "integer\n%d\n" i
                   | String(i) -> Printf.bprintf outbuf "string\n%s\n" (String.sub i 1 ((String.length i) - 2))
		   | Plus -> Printf.bprintf outbuf "plus\n"
                   | Minus -> Printf.bprintf outbuf "minus\n"
		   | Times -> Printf.bprintf outbuf "times\n"
                   | At -> Printf.bprintf outbuf "at\n"
                   | Case -> Printf.bprintf outbuf "case\n"
                   | Esac -> Printf.bprintf outbuf "esac\n"
                   | Class -> Printf.bprintf outbuf "class\n"
                   | Colon -> Printf.bprintf outbuf "colon\n"
                   | Comma -> Printf.bprintf outbuf "comma\n"
                   | Divide -> Printf.bprintf outbuf "divide\n"
                   | Dot -> Printf.bprintf outbuf "dot\n"
                   | Else -> Printf.bprintf outbuf "else\n"
                   | Equals -> Printf.bprintf outbuf "equals\n" 
                   | False -> Printf.bprintf outbuf "false\n"
                   | True -> Printf.bprintf outbuf "true\n"
                   | If -> Printf.bprintf outbuf "if\n" 
                   | Fi -> Printf.bprintf outbuf "fi\n"
                   | Then -> Printf.bprintf outbuf "then\n" 
                   | In -> Printf.bprintf outbuf "in\n" 
                   | Inherits -> Printf.bprintf outbuf "inherits\n" 
                   | Isvoid -> Printf.bprintf outbuf "isvoid\n"                 
                   | Larrow -> Printf.bprintf outbuf "larrow\n" 
                   | Rarrow -> Printf.bprintf outbuf "rarrow\n"
                   | Lbrace -> Printf.bprintf outbuf "lbrace\n"
                   | Rbrace -> Printf.bprintf outbuf "rbrace\n"
                   | Lparen -> Printf.bprintf outbuf "lparen\n"
                   | Rparen -> Printf.bprintf outbuf "rparen\n"
                   | Le -> Printf.bprintf outbuf "le\n"
                   | Let -> Printf.bprintf outbuf "let\n"
                   | Loop -> Printf.bprintf outbuf "loop\n"
                   | Pool -> Printf.bprintf outbuf "pool\n"
                   | Lt -> Printf.bprintf outbuf "lt\n"
                   | New -> Printf.bprintf outbuf "new\n" 
                   | Not -> Printf.bprintf outbuf "not\n"   
                   | Of -> Printf.bprintf outbuf "of\n"   
                   | Semi -> Printf.bprintf outbuf "semi\n"
                   | Tilde -> Printf.bprintf outbuf "tilde\n"           
                   | While -> Printf.bprintf outbuf "while\n"  
                   | Identifier(i) -> Printf.bprintf outbuf "identifier\n%s\n" i
                   | Type(i) -> Printf.bprintf outbuf "type\n%s\n" i
              end
         done 
        with | Eof -> begin       (*exception functions*)
               let filename = Sys.argv.(1) ^ "-lex" in
               let file_handle = open_out filename in
               Printf.fprintf file_handle "%s" (Buffer.contents outbuf) ;
               close_out file_handle ;
               exit 0 
             end

             | SingleRcomment -> begin
               Printf.printf "ERROR: %d: Lexer: comment without left parenthese\n" !line_number;
               exit 1
             end

             | _ -> begin
               Printf.printf "ERROR: %d: Lexer: invalid character: %c\n" !line_number (Lexing.lexeme_char lexbuf 0);
               exit 1
             end
end ;;
main () ;;
}

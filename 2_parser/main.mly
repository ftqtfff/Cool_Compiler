%{ (* The header section is for type declaration *)
open Printf (*import module*)
type identifier = string * string (* line number + lexeme *)
type cool_class = 
    | ClassNoInherits of identifier * (feature list)
    | ClassInherits of identifier * string * identifier * (feature list) (* the middle string corresponds to the token inherits *)
and feature = 
    | AttributeNoInit of identifier * identifier
    | AttributeInit of identifier * identifier * exp
    | Method of identifier * (formal list) * identifier * exp

and formal = identifier * identifier

and binding = 
    | BindingNoInit of identifier * identifier
    | BindingInit of identifier * identifier * exp

and caseElem = identifier * identifier * exp

and exp_inner = 
    | EPlus of exp * exp
    | ETimes of exp * exp
    | EDivide of exp * exp
    | EMinus of exp * exp
    | EInteger of string
    | EString of string
    | EIdentifier of identifier
    | EAssign of identifier * exp 
    | EDynamic_dispatch of exp * identifier * (exp list)
    | EStatic_dispatch of exp * identifier * identifier * (exp list)
    | ESelf_dispatch of identifier * (exp list)
    | EIf of exp * exp * exp
    | EWhile of exp * exp
    | EBlock of (exp list)
    | ENew of identifier
    | EIsvoid of exp
    | ELt of exp * exp
    | ELe of exp * exp
    | EEquals of exp * exp
    | ENot of exp
    | ENegate of exp 
    | ETrue
    | EFalse
    | ELet of (binding list) * exp
    | ECase of exp * (caseElem list)




and exp = string * exp_inner (* string = line number *)
type cool_program = cool_class list
%}


/* The line number is represented as a string */
/* The lexeme is represented as a string */
/* Convention: uppercase is token/terminal, lowercase is non-terminal. */

%token <string> CLASS LBRACE RBRACE LPAREN RPAREN AT CASE ESAC SEMI COLON LARROW RARROW INHERITS COMMA DOT ELSE TRUE FALSE IF FI THEN IN ISVOID LET LOOP POOL NEW NOT OF WHILE
%token <string * string> INTEGER
%token <string * string> STRING IDENTIFIER TYPE
%token <string> LE LT EQUALS 
%token <string> PLUS MINUS 
%token <string> TIMES DIVIDE 
%token <string> TILDE 
%token EOF


%start cool_program_rule /*the entry point*/
%type <cool_program> cool_program_rule

%%
cool_program_rule: class_list EOF { $1 }
;

class_list : /*nothing*/  { [] }
           | cool_class SEMI class_list { $1 :: $3 }   
           ;  

cool_class : CLASS TYPE LBRACE feature_list RBRACE { ClassNoInherits($2, $4) }  
           | CLASS TYPE INHERITS TYPE LBRACE feature_list RBRACE { ClassInherits($2, $3, $4, $6) }
           ;

feature_list : /* nothing */   { [] }
             | feature SEMI feature_list { $1 :: $3 }
             ;

feature : IDENTIFIER COLON TYPE { AttributeNoInit($1, $3) }
        | IDENTIFIER COLON TYPE LARROW exp { AttributeInit($1, $3, $5) }
        | IDENTIFIER LPAREN formal_list RPAREN COLON TYPE LBRACE exp RBRACE { Method($1, $3, $6, $8) }
        ;

binding_tail : /* nothing */ { [] }
             | COMMA binding binding_tail { $2 :: $3 }
             ;

binding : IDENTIFIER COLON TYPE { BindingNoInit($1, $3) } 
        | IDENTIFIER COLON TYPE LARROW exp  { BindingInit($1, $3, $5) }
        ;

caseElem_list : /* nothing */ { [] }
              | caseElem SEMI caseElem_list { $1 :: $3 }
              ;

caseElem : IDENTIFIER COLON TYPE RARROW exp { ($1, $3, $5) } 
;


formal_list : /* nothing */ { [] }
            | formal formal_tail {$1 :: $2}
            ;

formal_tail : /* nothing */ { [] }
            | COMMA formal formal_list { $2 :: $3 }
            ;

formal : IDENTIFIER COLON TYPE { ($1, $3) } 
;

exp_list :  /* nothing */ { [] }
         | exp exp_tail {$1 :: $2}
         ;

exp_tail : /* nothing */ { [] }
         | COMMA exp exp_tail { $2 :: $3 }
         ;

exp_normal : exp SEMI { $1 :: [] }
           | exp SEMI exp_normal { $1 :: $3 }
           ;

exp : IDENTIFIER LARROW exp { let line, _ = $1 in (line, EAssign($1, $3)) }
    | exp AT TYPE DOT IDENTIFIER LPAREN exp_list RPAREN { let line, _ = $1 in (line, EStatic_dispatch($1, $3, $5, $7) ) }
    | exp DOT IDENTIFIER LPAREN exp_list RPAREN { let line, _ = $1 in (line, EDynamic_dispatch($1, $3, $5) ) }
    | IDENTIFIER LPAREN exp_list RPAREN {let line, _ = $1 in (line, ESelf_dispatch($1, $3) ) }
    | IF exp THEN exp ELSE exp FI { let line = $1 in (line, EIf($2, $4, $6) ) }
    | WHILE exp LOOP exp POOL {let line = $1 in (line, EWhile($2, $4) )}
    | LBRACE exp_normal RBRACE {let line = $1 in (line, EBlock($2) ) }
    | LET binding binding_tail IN exp {let line = $1 in (line, ELet($2::$3, $5) ) }
    | CASE exp OF caseElem caseElem_list ESAC {let line = $1 in (line, ECase($2, $4 :: $5) )}
    | NEW TYPE {let line = $1 in (line, ENew($2) )}
    | ISVOID exp {let line = $1 in (line, EIsvoid($2) )} 
    | exp PLUS exp  { let line, _ = $1 in ( line, EPlus($1, $3) ) }
    | exp MINUS exp { let line, _ = $1 in ( line, EMinus($1, $3) ) }
    | exp TIMES exp { let line, _ = $1 in ( line, ETimes($1, $3) ) }
    | exp DIVIDE exp { let line, _ = $1 in ( line, EDivide($1, $3) ) }
    | TILDE exp { let line = $1 in ( line, ENegate($2) ) }
    | exp LT exp { let line, _ = $1 in (line, ELt($1, $3)) }
    | exp LE exp { let line, _ = $1 in (line, ELe($1, $3)) }
    | exp EQUALS exp { let line, _ = $1 in (line, EEquals($1, $3))}
    | NOT exp { let line = $1 in (line, ENot($2)) }
    | LPAREN exp RPAREN { $2 }
    | IDENTIFIER {  let line, _ = $1 in ( line, EIdentifier($1) )}   
    | INTEGER       { let line, int_string = $1 in ( line, EInteger(int_string) ) }  
    | STRING        { let line, str_string = $1 in ( line, EString(str_string) ) }
    | TRUE { let line = $1 in ( line, ETrue ) }
    | FALSE { let line = $1 in (line, EFalse) }            
    ;



%%     

let read_tokens token_filename = 
  let fin = open_in token_filename in 
  let tokens_queue = Queue.create () in
  let get_line () = String.trim (input_line fin) in
  (try while true do
    let l = get_line () in      (* l denotes line number *)
    let token_type = get_line () in
    let token = match token_type with
    | "class" -> CLASS(l)
    | "semi" -> SEMI(l)
    | "colon" -> COLON(l)
    | "lbrace" -> LBRACE(l)
    | "rbrace" -> RBRACE(l)
    | "plus" -> PLUS(l)
    | "minus" -> MINUS(l)
    | "times" -> TIMES(l)
    | "divide" -> DIVIDE(l)
    | "larrow" -> LARROW(l)
    | "rarrow" -> RARROW(l)
    | "lparen" -> LPAREN(l)
    | "rparen" -> RPAREN(l)
    | "at" -> AT(l)
    | "case" -> CASE(l)
    | "esac" -> ESAC(l)
    | "inherits" -> INHERITS(l)
    | "comma" -> COMMA(l)
    | "dot" -> DOT(l)
    | "else" -> ELSE(l)
    | "equals" -> EQUALS(l)
    | "true" -> TRUE(l)
    | "false" -> FALSE(l)
    | "if" -> IF(l)
    | "fi" -> FI(l)
    | "then" -> THEN(l)
    | "in" -> IN(l)
    | "isvoid" -> ISVOID(l)
    | "le" -> LE(l)
    | "let" -> LET(l) 
    | "loop" -> LOOP(l)
    | "pool" -> POOL(l)
    | "lt" -> LT(l)
    | "new" -> NEW(l)
    | "not" -> NOT(l)
    | "of" -> OF(l)
    | "tilde" -> TILDE(l)
    | "while" -> WHILE(l)
    | "integer" -> INTEGER(l, get_line()) (* INTEGER token's type is <string * string> *)
    | "string" -> STRING(l, get_line())
    | "identifier" -> IDENTIFIER(l, get_line())
    | "type" -> TYPE(l, get_line())

    | _ -> begin 
      Printf.printf "unexpected token type: %s/n" token_type ;
      exit 1
    end 
    in
    Queue.add (l,token) tokens_queue (* store line number and token *)
  done with _ -> () );
  close_in fin ;
  tokens_queue
       
let main () = begin
  (*Read in the Tokens from Lexer files*)
  let token_filename = Sys.argv.(1) in
  let tokens_queue = read_tokens token_filename in 
  let lexbuf = Lexing.from_string "" in (*fake up a lexer*)
  let last_line_number = ref "1" in
  let lexer_token lb = (* This is a function pretended to be a lexer, it returns the line number and the corresponding token at each time *)
    if Queue.is_empty tokens_queue then  
       EOF
    else begin
       let line_number, next_token = Queue.take tokens_queue in
       last_line_number := line_number ;
       next_token (* return PA2 token to OCaml's PA3 Parser *)
    end
  in
  let ast = 
    try (* Do the Parsing *)
      cool_program_rule lexer_token lexbuf       
    with _ -> begin
      printf "ERROR: %s: Parser: syntax error\n" !last_line_number;
      exit 0
    end
  in
  (*Serialization: convert file xxx.cl-lex into xxx.cl-ast *)
  let output_filename = (Filename.chop_extension Sys.argv.(1)) ^ ".cl-ast" in
  let f = open_out output_filename in
  let rec output_cool_program ast = output_class_list ast
  and output_class_list ast = 
      fprintf f "%d\n" (List.length ast) ; 
      List.iter output_class ast

  and output_class ast = 
    match ast with
   | ClassNoInherits(class_name, class_features) -> 
     output_identifier class_name ;
     fprintf f "no_inherits\n" ; 
     fprintf f "%d\n" (List.length class_features) ;
     List.iter output_feature class_features
   | ClassInherits(class_name, class_inherits, class_nameInherit, class_features) ->
     output_identifier class_name ; 
     fprintf f "inherits\n" ;
     output_identifier class_nameInherit ; 
     fprintf f "%d\n" (List.length class_features) ;
     List.iter output_feature class_features   (* output each element of the list class_features *)

   and output_identifier (line_number, the_string_lexeme) =
       fprintf f "%s\n%s\n" line_number the_string_lexeme

   and output_feature ast_feature = 
     match ast_feature with
     | AttributeNoInit(attr_name, attr_type) ->  
       fprintf f "attribute_no_init\n" ; 
       output_identifier attr_name ; 
       output_identifier attr_type 
     | AttributeInit(attr_name, attr_type, init_exp) ->
       fprintf f "attribute_init\n" ;
       output_identifier attr_name ;
       output_identifier attr_type ;
       output_exp init_exp
     | Method(meth_name, formalList, meth_type, body_exp) ->
       fprintf f "method\n" ;
       output_identifier meth_name ; 
       fprintf f "%d\n" (List.length formalList) ; 
       List.iter output_formal formalList;
       output_identifier meth_type ;
       output_exp body_exp ;
    
   and output_formal (formalName, formalType) = 
       output_identifier formalName;
       output_identifier formalType

   and output_letBinding ast_bind = 
     match ast_bind with
     | BindingNoInit(var, typ) ->
       fprintf f "let_binding_no_init\n";
       output_identifier var;
       output_identifier typ
     | BindingInit(var, typ, value) ->
       fprintf f "let_binding_init\n";
       output_identifier var;
       output_identifier typ;
       output_exp value

   and output_case (caseVar, caseType, caseBody) =
       output_identifier caseVar;
       output_identifier caseType;
       output_exp caseBody

    and output_exp (line, inner_exp) =
     fprintf f "%s\n" line; (* output line number first *)
     match inner_exp with
     | EInteger(int_str) -> fprintf f "integer\n%s\n" int_str 
     | EString(string_str) -> fprintf f "string\n%s\n" string_str 
     | EIdentifier(var) -> 
       fprintf f "identifier\n";
       output_identifier var
     | EPlus(a,b) ->
       fprintf f "plus\n" ;
       output_exp a;
       output_exp b
     | EMinus(a,b) ->
       fprintf f "minus\n" ; 
       output_exp a; 
       output_exp b
     | ETimes(a,b) -> 
       fprintf f "times\n" ;
       output_exp a;
       output_exp b
     | EDivide(a,b) ->
       fprintf f "divide\n" ;
       output_exp a;
       output_exp b
     | EAssign(a,rhs) ->
       fprintf f "assign\n" ;
       output_identifier a;
       output_exp rhs
     | EDynamic_dispatch(e, met, argList) ->
       fprintf f "dynamic_dispatch\n" ;
       output_exp e;
       output_identifier met;
       fprintf f "%d\n" (List.length argList) ;
       List.iter output_exp argList
     | EStatic_dispatch(e, typ, met, argList) ->
       fprintf f "static_dispatch\n" ;
       output_exp e;
       output_identifier typ;
       output_identifier met;
       fprintf f "%d\n" (List.length argList) ;
       List.iter output_exp argList
     | ESelf_dispatch(met, argList) ->
       fprintf f "self_dispatch\n" ;
       output_identifier met;
       fprintf f "%d\n" (List.length argList) ;
       List.iter output_exp argList
     | EIf(predicate, the, els) ->
       fprintf f "if\n" ;
       output_exp predicate;
       output_exp the;
       output_exp els
     | EWhile(predicate, body) ->
       fprintf f "while\n"; 
       output_exp predicate;
       output_exp body
     | EBlock(bodyList) ->
       fprintf f "block\n";
       fprintf f "%d\n" (List.length bodyList) ;
       List.iter output_exp bodyList
     | ENew(clas) ->
       fprintf f "new\n";
       output_identifier clas
     | EIsvoid(e) ->
       fprintf f "isvoid\n" ;
       output_exp e
     | ELt(a,b) ->
       fprintf f "lt\n";
       output_exp a;
       output_exp b
     | ELe(a,b) ->
       fprintf f "le\n";
       output_exp a;
       output_exp b
     | EEquals(a,b) ->
       fprintf f "eq\n";
       output_exp a;
       output_exp b
     | ENot(a) ->
       fprintf f "not\n";
       output_exp a
     | ENegate(a) ->
       fprintf f "negate\n";
       output_exp a
     | ETrue ->
       fprintf f "true\n";
     | EFalse ->
       fprintf f "false\n";
     | ELet(bindingList, letBody) ->
       fprintf f "let\n";
       fprintf f "%d\n" (List.length bindingList) ;
       List.iter output_letBinding bindingList; 
       output_exp letBody
     | ECase(caseExpr, caseElemList) ->
       fprintf f "case\n";
       output_exp caseExpr;
       fprintf f "%d\n" (List.length caseElemList) ;
       List.iter output_case caseElemList
   in

   output_cool_program ast ; 

   close_out f

end;;

main () ;;


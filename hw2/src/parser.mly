%{
  open Tree;;
%}
%token <string> VAR
%token IMPL AND OR NOT
%token OPEN CLOSE
%token EOF
%token COMMA
%token INTO
%token PROOF
%left COMMA
%nonassoc INTO
%nonassoc PROOF
%right IMPL
%left OR
%left AND
%nonassoc NOT
%start main
%type <Tree.tree> main
%%
main:
        expr EOF           { $1 }
expr:
        VAR                { Var ($1) }
        |OPEN expr CLOSE   { $2 }     
        |NOT expr          { Neg ($2) }  
        |expr IMPL expr    { Binop (Impl, $1, $3) }
        |expr AND expr     { Binop (Conj, $1, $3) }
        |expr OR expr      { Binop (Disj, $1, $3) }
        |expr COMMA expr   { Binop (Comma, $1, $3) }
        |expr INTO expr    { Binop (Into, $1, $3) }
        |INTO expr         { Binop (Into, None, $2) }
        |expr PROOF expr   { Binop (Proof, $1, $3) }
        |PROOF expr        { Binop (Proof, None, $2) }
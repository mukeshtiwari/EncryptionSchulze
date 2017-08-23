%token <int> INT
%token <char> CAND
%token LPAREN
%token RPAREN
%token COMMA
%token SEMI
%token NEWLINE
%token EOF


%start <(char * int) list list> prog

%%

prog:
 | EOF {[]}         
 | v = stmtone; NEWLINE; ds = prog EOF {v :: ds}
 
stmtone:
 | vs = separated_nonempty_list (SEMI, stmt) {vs};

stmt: LPAREN; s = CAND; COMMA; n = INT; RPAREN {(s, n)}

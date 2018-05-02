%token <int> INT
%token <char> CAND
%token LPAREN
%token RPAREN
%token COMMA
%token SEMI
%token NEWLINE
%token EOF


%start <(char * char * (string * string)) list list> prog

%%

prog:
 | EOF {[]}         
 | v = stmtone; NEWLINE; ds = prog EOF {v :: ds}
 
stmtone:
 | vs = separated_nonempty_list (SEMI, stmt) {vs};

stmt: LPAREN; s = CAND; COMMA; t = CAND; COMMA; LPAREN; n = string; COMMA; m = string; RPAREN; RPAREN {(s, t, (n, m))}

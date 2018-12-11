{
open Parser

}

rule lexeme = parse
 |['\n' '\r']+ {NEWLINE}
 |[' ' '\t']+ {lexeme lexbuf}
 |['0' - '9']+ as strnum { STRING strnum }
 |'A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J' | 'K' | 'L' | 'N' | 'P' | 'Q' | 'R' | 'T' | 'U' | 'V' | 'X' (*| 'Y' | 'Z'*) as v {CAND v}
 |'('  { LPAREN }
 |')' { RPAREN } 
 |';' { SEMI }
 |',' { COMMA }
 |eof { EOF }


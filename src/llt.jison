/* description: Parses end executes mathematical expressions. */

/* lexical grammar */
%lex

%%
"%".*                                       /* skip comment    */
\s+                                         /* skip whitespace */
"-o"                                        return '-o';
"*"                                         return '*';
":"                                         return ':';
"."                                         return '.';
"("                                         return '(';
")"                                         return ')';
"{"                                         return '{';
"}"                                         return '}';
","                                         return ',';
"="                                         return '=';
"<-"                                        return '<-';
"context"                                   return 'context';
[\w\/]+                                     return 'WORD';
<<EOF>>                                     return 'EOF';

/lex

/* operator associations and precedence */

%start program

%% /* language grammar */

program
    : statements EOF
      { return yy.LLT.db; }
    ;

statements
    : statement "." statements
    | statement "."
    ;

words
    : WORD words
      { $$ = [$1].concat($2) }
    | "(" words ")" words
      { $$ = [$2].concat($4) }
    | "(" words ")"
      { $$ = [$2]; }
    | WORD
      { $$ = [$1]; }
    ;

typing_statement
    : words ":" WORD
      { $$ = $1.concat([$3])}
    ;

bwd_def
    : words "<-" bwd_def
      { $$ = [$1].concat($3) }
    | words
      { $$ = [$1] }
    ;

fwd_def
    : words "-o" fwd_def
      { $$ = ["-o", $1].concat([$3]) }
    | words "*" fwd_def
      { $$ = ["*", $1].concat([$3]) }
    | words "-o" words
      { $$ = ["-p", $1].concat([$3]) }
    | words "*" words
      { $$ = ["*", $1].concat([$3]) }
    ;

context_def
    : "context" WORD "=" "{" ctx_ressources_def "}"
      { $$ = yy.LLT.ctx_def($2, $5) }
    ;

ctx_ressources_def
    : words "," ctx_ressources_def
      { $$ = [$1].concat($3) }
    | words
      { $$ = [$1] }
    ;

statement
    : typing_statement     //                          typing def
      { yy.LLT.type($1) }
    | bwd_def              //                  bwd definition
      { yy.LLT.bwd_def($1) }
    | fwd_def
      { yy.LLT.fwd_def($1) }
    | context_def
    ;

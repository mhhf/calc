/* description: Parses end executes mathematical expressions. */

/* lexical grammar */
%lex

%%
"%".*                                       /* skip comment    */
\s+                                         /* skip whitespace */
"-o"                                        return '-o';
"*"                                         return '*';
"&"                                         return '&';
"!"                                         return '!';
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
"stage"                                     return 'stage';
[\w\/]+                                     return 'WORD';
<<EOF>>                                     return 'EOF';

/lex

/* operator associations and precedence */
%left "-o"
%left "*"
%left "&"
%left "!"

%start program

%% /* language grammar */

program
    : statements EOF
      { return yy.LLT.db; }
    ;

statements
    : statement "." statements
    | statement "."
    | fwd_def statements
    | context_def "." statements
    | fwd_def
    | context_def "."
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

Atprop
    : words
      { $$ = yy.LLT.toNode($1); }
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

fwd_rules
    : Formula "."
      { yy.LLT.fwd_def($1) }
    | Formula "." fwd_rules
      { yy.LLT.fwd_def($1) }
    ;


fwd_def
    : "stage" WORD "=" "{" fwd_rules "}"
    ;
    // : words "-o" fwd_def
    //   { $$ = ["-o", $1].concat([$3]) }
    // | words "*" fwd_def
    //   { $$ = ["*", $1].concat([$3]) }
    // | words "-o" words
    //   { $$ = ["-p", $1].concat([$3]) }
    // | words "*" words
    //   { $$ = ["*", $1].concat([$3]) }
    // ;

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
    ;

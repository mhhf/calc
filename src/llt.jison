/* description: Parses end executes mathematical expressions. */

/* lexical grammar */
%lex

%%
"%".*                                       /* skip comment    */
\s+                                         /* skip whitespace */
":"                                         return ':';
"."                                         return '.';
"("                                         return '(';
")"                                         return ')';
"<-"                                        return '<-';
[\w\/]+                                     return 'WORD';
<<EOF>>                                     return 'EOF';

/lex

/* operator associations and precedence */

%start program

%% /* language grammar */

program
    : statements EOF
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

statement
    : typing_statement     //                        typing def
      { yy.LLT.type($1) }
    | bwd_def              //                    bwd definition
      { yy.LLT.bwd_def($1) }
    ;

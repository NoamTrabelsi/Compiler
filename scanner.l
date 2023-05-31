%{
    #include <stdio.h>
    #include <string.h>
    #include <stdlib.h>
    #include "y.tab.h"
    int yyerror(const char* s);

%}
%option yylineno

%%
"int*" return INTP;
"char*" return CHARP;
"real*"  return REALP;
bool  return BOOL;
char  return CHAR;
int  return INT;
real  return REAL;
string  return STRING;
if  return IF;
else  return ELSE;
while  return WHILE;
for  return FOR;
var  return VAR;
"return"  return RETURN;
"null"  return EMPTY;
void  return VOID;
function return FUNCTION;
arg-> return ARGSFUNC;
do  return DO;
true  return TRUE;
false  return FALSE;
==  return EQUAL;
&&  return AND;
"<=" return SMALLEQ;
">=" return BIGEQ;
!= return NOTEQUAL;
! return NOT;
"||" return OR;
[-]?0[xX][0-9ABCDEF]+|[0-9]+ {yylval.string = strdup(yytext); return INTNUM;}
[-]?[0-9]*[.]?([Ee][+-]?)?[0-9]+ {yylval.string = strdup(yytext); return REALNUM;}
\'(\\.|[^"\\])\' {yylval.string = strdup(yytext); return CHARVAL;}
\"(\\.|[^"\\])*\" {yylval.string = strdup(yytext); return STRINGVAL;}
[a-zA-Z]+[_0-9a-zA-Z]* {yylval.string = strdup(yytext); return VARNAME;}
"/*"[ -~\n\t]*"*/"
[\n \t]
. {return yytext[0];}

%%


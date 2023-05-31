%{
#include<stdio.h>
#include<string.h>
#include<stdlib.h>
#include "lex.yy.c"
#include "List.c"

#define ERRORV -1
#define INTV 0
#define REALV 1
#define BOOLV 2
#define CHARV 3
#define STRINGV 4
#define CHARPV 5
#define INTPV 6
#define REALPV 7
#define FUNCINTV 8
#define FUNCREALV 9
#define FUNCCHARV 10
#define FUNCBOOLV 11
#define FUNCINTPV 12
#define FUNCREALPV 13
#define FUNCCHARPV 14
#define VOIDV 15
#define NULLV 16

int yylex(void);
int yyerror();
int varindex = 0;
int labelindex = 0;


typedef struct node
{
	char *token;
	struct node *left;
	struct node *right;
	char* code;
	char* var;
	//int bytes;
	char* trueLabel;
	char* falseLabel;
} node;

void setVar(node* curNode, char* newVar){
	curNode->var = (char*)malloc(strlen(newVar)+1);
	strcpy(curNode->var, newVar);
}

void setCode(node* curNode, char* newCode){
	curNode->code = (char*)malloc(strlen(newCode)+1);
	strcpy(curNode->code, newCode);
}

char* combineStrings(char** charray, int size){
	int sum = 0;
	for (int i =0;i<size;i++){
		sum+= strlen(charray[i]);
	}
	char* output = malloc(sizeof(char)*sum+1);
	int index = 0;
	for (int i=0;i<size;i++){
		for(int j=0; charray[i][j] != '\0'; j++){
    			output[index++] = charray[i][j];
    		}
    	}
    	output[sum] = '\0';
    	return output;
}


char* freshVar(){
	char* num = (char*) malloc(1);
	char* t = (char*) malloc(sizeof(char));
	strcpy(t,"t");
	sprintf(num,"%d", varindex++);
	return strcat(t,num);
}
char* freshLabel(){
	char* num = (char*) malloc(1);
	char* t = (char*) malloc(sizeof(char));
	strcpy(t,"L");
	sprintf(num,"%d", labelindex++);
	return strcat(t,num);
}


node* TotalTree;
list* SymbolTable;

int argsPop(node*);
char* shortCircuit(node*, char* ,char*);
node *mknode(char *token,node *left,node *right);
void printtree(node *tree, int);
char* scanTree(list*, node*, int);
int scanST(list*, char*);
int scanHead(list*, char*);
int getType(node*, list*);
void functionArgs(node*, list*, int);
void freeTree(node*);
int* funCall(node*, list* , int* , int*);
argsL* getArgs(list*, char*);
int checkFuncType(node*, int,list*,int*);
int checkMain(list*,node*);
void To3ADCode(node*);
int errorA = 0;
int mainCount=0;
%}
%union{
	char* string;
	struct node* node;
}

%define parse.lac full
%token <string>  ARGSFUNC FUNCTION BOOL CHAR INT REAL STRING INTP CHARP REALP IF ELSE WHILE FOR VAR RETURN EMPTY VOID DO TRUE FALSE INTNUM REALNUM VARNAME EQUAL AND SMALLEQ BIGEQ NOTEQUAL NOT OR CHARVAL STRINGVAL

%type <node> start s EXP TER FRQ ID MINUS PLUS MULVAL FUNCTIONCALL FUNCARGS FUNCMOREARGS OPERATOR LOGICOP ASSIGN ASSIGNVAL STARTDEC STRINGVALUE DECLARATION DECLARATION2 DECLARATION3 PTYPE TYPE CONTDEC STRINGDEC MORESTRING REST  RETURNARGS ENDSTRINGDEC BLOCK TERMS TERMS2  FUNCDECLERATION  ARGS MOREVARS MOREARGS LOOP MOREDEC st ONESTATE FUNCBLOCK FUNCBLOCK2 FUNCTYPE
%right '+' '-' 
%right '*' '/'  

%%
realStart: start { TotalTree = $1;}

start: start FUNCDECLERATION {$$=mknode("CODE",$1,$2);} 
| {$$=mknode("EMPTY",NULL,NULL);}
s: s st {$$=mknode("",$1,$2);}
| {$$=mknode("EMPTY",NULL,NULL);}

st: ASSIGN ';' {$$=$1;}
	| FUNCDECLERATION {$$=$1;}
	| RETURNARGS {$$=$1;}
	| BLOCK  {$$=$1;}
	| TERMS {$$=$1;}
	| FUNCTIONCALL ';' {$$=$1;}
	| LOOP  {$$=$1;}
	;


LOOP: FOR '(' ASSIGN ';' EXP ';' ASSIGN ')' ONESTATE {$$=mknode("FOR",mknode("",$3,$5),mknode("",$7,$9));}
	|WHILE '(' EXP ')' ONESTATE {$$=mknode("WHILE",$3,$5);}
	| DO BLOCK WHILE '(' EXP ')' ';' {$$=mknode("DO",$2,mknode("WHILE",$5,NULL));}


FUNCDECLERATION: FUNCTION VARNAME '(' ARGS ')' ':' VOID FUNCBLOCK2 {$$=mknode("VOID FUNC",mknode($2,NULL,NULL),mknode("FUNC",$4,$8));}
				|FUNCTION VARNAME '(' ARGS ')' ':' FUNCTYPE  FUNCBLOCK {$$=mknode(strcat($7->token," FUNC"),mknode($2,NULL,NULL),mknode("FUNC",$4,$8));}
				|FUNCTION VARNAME '(' ARGS ')' ':' PTYPE  FUNCBLOCK {$$=mknode(strcat($7->token," FUNC"),mknode($2,NULL,NULL),mknode("FUNC",$4,$8));}

FUNCTYPE:INT {$$=mknode("INT",NULL,NULL);}
	| REAL {$$=mknode("REAL",NULL,NULL);}
	| BOOL {$$=mknode("BOOL",NULL,NULL);}
	| CHAR {$$=mknode("CHAR",NULL,NULL);}
ARGS: 
	ARGSFUNC VARNAME MOREVARS ':' TYPE MOREARGS {$$=mknode($5->token,mknode($2,$3,NULL),$6);}
	|ARGSFUNC VARNAME MOREVARS ':' PTYPE MOREARGS {$$=mknode($5->token,mknode($2,$3,NULL),$6);}
	| {$$=mknode("EMPTY",NULL,NULL);}

MOREVARS: ',' VARNAME MOREVARS {$$=mknode(",",mknode($2,$3,NULL),NULL);}
	|{$$=mknode("EMPTY",NULL,NULL);}

MOREARGS : 
	';' ARGSFUNC VARNAME MOREVARS ':' TYPE MOREARGS {$$=mknode($6->token,mknode($3,$4,NULL),$7);}
	|';' ARGSFUNC VARNAME MOREVARS ':' PTYPE MOREARGS {$$=mknode($6->token,mknode($3,$4,NULL),$7);}
	|{$$=mknode("EMPTY",NULL,NULL);}

BLOCK:  '{' MOREDEC s '}' {$$=mknode("BLOCK",$2,$3);}
FUNCBLOCK:  '{' MOREDEC s RETURNARGS '}' {$$=mknode("BODY",$2,mknode("",$3,$4));}
FUNCBLOCK2:'{' MOREDEC s '}' {$$=mknode("BODY",$2,$3);}

TERMS: IF '(' EXP ')' ONESTATE TERMS2 {$$=mknode("IF",$3,mknode("",$5,$6));}

ONESTATE : st {$$=$1;}
	| STARTDEC{$$=$1;}
	
TERMS2: ELSE ONESTATE {$$=mknode("ELSE",$2,NULL);}
	|{$$=mknode("EMPTY",NULL,NULL);}


RETURNARGS: RETURN EXP ';' {$$=mknode("RET",$2,NULL);}

MOREDEC: MOREDEC STRINGDEC {$$=mknode("",$1,$2);}
	| MOREDEC STARTDEC {$$=mknode("",$1,$2);}
	| {$$=mknode("EMPTY",NULL,NULL);}

STRINGDEC: STRING VARNAME '[' EXP ']' REST {$$=mknode("STRING", mknode($2,mknode("[]",$4,NULL),NULL),$6);}

REST: MORESTRING ENDSTRINGDEC ';' {$$=mknode("",$1,$2);}

MORESTRING: ',' VARNAME '[' EXP ']' MORESTRING {$$=mknode(",",mknode($2,mknode("[]",$4,NULL),NULL),$6);}
	| {$$=mknode("EMPTY",NULL,NULL);}

ENDSTRINGDEC: '=' STRINGVALUE {$$=mknode("=",$2,NULL);}
	| {$$=mknode("EMPTY",NULL,NULL);}
	| '=' FUNCTIONCALL {$$=mknode("=",$2,NULL);}

STARTDEC: VAR CONTDEC {$$=$2;}

CONTDEC: DECLARATION ':' TYPE ';'   {$$=mknode($3->token,$1,NULL);}
	| DECLARATION ':' PTYPE ';'  {$$=mknode($3->token,$1,NULL);}
 
DECLARATION: VARNAME DECLARATION2 {$$=mknode($1,$2,NULL);}
	| VARNAME DECLARATION3 {$$=mknode($1,$2,NULL);}

DECLARATION2: ',' DECLARATION  {$$=mknode(",",$2,NULL);}
	| {$$=mknode("EMPTY",NULL,NULL);}

DECLARATION3: '=' EXP DECLARATION2 {$$=mknode("=",$2,$3);}

PTYPE: INTP {$$=mknode("INT*",NULL,NULL);}
	| CHARP {$$=mknode("CHAR*",NULL,NULL);}
	| REALP {$$=mknode("REAL*",NULL,NULL);}

TYPE: INT {$$=mknode("INT",NULL,NULL);}
	| REAL {$$=mknode("REAL",NULL,NULL);}
	| BOOL {$$=mknode("BOOL",NULL,NULL);}
	| CHAR {$$=mknode("CHAR",NULL,NULL);}
	| STRING  {$$=mknode("STRING",NULL,NULL);}


ASSIGN: VARNAME '=' ASSIGNVAL  {$$=mknode("VARNAMEVAL", mknode($1,NULL,NULL),mknode("ASSIGN",$3,NULL));}
	| VARNAME '[' EXP ']' '=' ASSIGNVAL {$$=mknode("VARNAMEVAL",mknode($1,mknode("[]",$3,NULL),NULL),mknode("ASSIGN",$6,NULL));}
	| '*' VARNAME '=' ASSIGNVAL {$$=mknode("POINTER",mknode("VARNAMEVAL",mknode($2,NULL,NULL),NULL),mknode("ASSIGN",$4,NULL));}


ASSIGNVAL: EXP {$$=mknode("",$1,NULL);}

STRINGVALUE: CHARVAL {$$=mknode("CHARVAL",mknode($1,NULL,NULL),NULL);}
	| STRINGVAL {$$=mknode("STRINGVAL",mknode($1,NULL,NULL),NULL);}

OPERATOR: '<' {$$=mknode("<",NULL,NULL);}
	| '>' {$$=mknode(">",NULL,NULL);}
	| EQUAL  {$$=mknode("==",NULL,NULL);}
	| SMALLEQ {$$=mknode("<=",NULL,NULL);}
	| BIGEQ {$$=mknode(">=",NULL,NULL);}
	| NOTEQUAL {$$=mknode("!=",NULL,NULL);}

LOGICOP: AND {$$=mknode("&&",NULL,NULL);}
	| OR {$$=mknode("||",NULL,NULL);}

EXP:TER'+'TER {$$=mknode("+",$1,$3);}
	|TER'-'TER {$$=mknode("-",$1,$3);}
	|TER {$$=$1;}
	|EXP LOGICOP TER {$$=mknode($2->token,$1,$3);}

TER:FRQ'*'FRQ {$$=mknode("*",$1,$3);}
	|FRQ'/'FRQ {$$=mknode("/",$1,$3);}
	|FRQ {$$=$1;}
	|TER OPERATOR FRQ {$$=mknode($2->token,$1,$3);}
 
FRQ:'('EXP')' {$$=$2;}
	|PLUS {$$=$1;}
	|MINUS {$$=$1;}
	|MULVAL {$$=mknode("POINTER",$1,NULL);}
	
ID:INTNUM {$$=mknode("INTNUM",mknode($1,NULL,NULL),NULL);}
	|REALNUM {$$=mknode("REALVAL",mknode($1,NULL,NULL),NULL);}
	|VARNAME {$$ = mknode("VARNAMEVAL",mknode($1,NULL,NULL),NULL);}//{$$ = mknode($1,NULL,NULL);}
	|'|'VARNAME'|' {$$=mknode("LEN",mknode("VARNAMEVAL",mknode($2,NULL,NULL),NULL),NULL);}
	|'|'STRINGVAL'|' {$$=mknode("LEN",mknode("STRINGVAL",mknode($2,NULL,NULL),NULL),NULL);}
	|VARNAME'['EXP']' {$$=mknode("VARNAMEVAL", mknode($1,NULL,NULL), mknode("[]",$3,NULL));}
	|TRUE {$$=mknode("BOOLEAN",mknode($1,NULL,NULL),NULL);}
	|FALSE {$$=mknode("BOOLEAN",mknode($1,NULL,NULL),NULL);}
	|FUNCTIONCALL {$$=$1;}
	|STRINGVALUE {$$=$1;}
	|EMPTY {$$=mknode("NULL",NULL,NULL);}
	|'&''('EXP')' {}
	|'&'VARNAME {$$=mknode("ADDRESS",mknode("VARNAMEVAL", mknode($2,NULL,NULL),NULL),NULL);}
	|'&'VARNAME'['EXP']' {$$=mknode("ADDRESS", mknode("VARNAMEVAL", mknode($2,NULL,NULL),NULL), mknode("[]",$4,NULL));}

MINUS:'-'ID {$$=$2;}

PLUS:'+'ID {$$=$2;}
	|ID {$$=$1;}
	|NOT EXP {$$=mknode("NOT",$2,NULL);}

MULVAL:'*'ID {$$=$2;}
	|'*''('EXP')' {$$=mknode("",$3,NULL);}

FUNCTIONCALL: VARNAME '(' FUNCARGS ')' {$$ = mknode("FUNC",mknode("VARNAMEVAL",mknode($1,NULL,NULL),NULL),$3);}

FUNCARGS: EXP FUNCMOREARGS {$$ = mknode("ARGS",$1,$2);}
	| {$$ = mknode("EMPTY",NULL,NULL);}

FUNCMOREARGS: ','EXP FUNCMOREARGS {$$=mknode("MOREARGS",$2,$3);}
	| {$$ = mknode("EMPTY",NULL,NULL);}



%%

int main(){
	printf("main\n");
	yyparse();
	//printtree(TotalTree,0);
	if(errorA)
		return 0;
	SymbolTable = BuildNode();
	char* msg = scanTree(SymbolTable, TotalTree,0);
	if(msg == NULL && mainCount >0){
		printtree(TotalTree,0);
		To3ADCode(TotalTree);

	}
	else if(msg != NULL)
		printf("%s",msg);
	else
		printf("there is no main\n");
	FreeList(SymbolTable);
	//freeTree(TotalTree);
	return 0;
}

void To3ADCode(node* tree){
	if(tree == NULL || (tree->left == NULL && tree->right== NULL && !strcmp(tree->token, "EMPTY")))
		return;
	To3ADCode(tree->left);
	To3ADCode(tree->right);
	if(tree->left == NULL && tree->right== NULL && strcmp(tree->token, "EMPTY")){
		setVar(tree, tree->token);
		setCode(tree, "");
	}
	if (tree->left !=NULL && tree->right == NULL || (tree->right !=NULL && !strcmp(tree->right->token, "EMPTY"))){
		setVar(tree, tree->left->var);
		setCode(tree, tree->left->code);
	}
	if (tree->right !=NULL && tree->left ==NULL){
		setVar(tree, tree->right->var);
		setCode(tree, tree->right->code);
	}
	if (tree->right !=NULL && tree->left !=NULL){
		char* newCode [] = {tree->left->code, tree->right->code};
		setCode(tree, combineStrings(newCode, 2));
	}
	if(!strcmp(tree->token,"INTNUM") || !strcmp(tree->token,"REALVAL") || !strcmp(tree->token,"VARNAMEVAL")|| !strcmp(tree->token,"BOOLVAL")|| !strcmp(tree->token,"POSITIVE")){
		setVar(tree, tree->left->var);
		setCode(tree, tree->left->code);
		if(tree->right != NULL && !strcmp(tree->right->token,"ASSIGN")){
			setVar(tree, tree->left->token);
			if(!strcmp(tree->right->left->left->token,"||") || !strcmp(tree->right->left->left->token,"&&")){
				char * trueL = (char*)malloc(1);
				strcpy(trueL,freshLabel());
				char * falseL = (char*)malloc(1);
				strcpy(falseL,freshLabel());
				char * restL = (char*)malloc(1);
				strcpy(restL,freshLabel());
				char* newCode [] = {shortCircuit(tree->right->left->left,trueL,falseL),"\n",trueL,":\t",tree->var, "=1\n\tgoto ",restL, "\n", falseL,":\t",tree->var, "=0\n", restL, ":"};
				setCode(tree, combineStrings(newCode,14));
			}
			else if (tree->left->left != NULL && !strcmp(tree->left->left->token,"[]")){
				setVar(tree->left->left, freshVar());
				char* newCode1 [] = {tree->left->left->code, "\t",tree->left->left->var, "=", tree->left->token, "+", tree->left->var, "\n\0"};
				setCode(tree->left->left, combineStrings(newCode1, 8));
				setVar(tree->left, tree->left->left->var);
				setCode(tree->left, tree->left->left->code);
				/*setVar(tree->left, freshVar());
				char* newCode [] = {tree->left->left->code,"\t",tree->left->var, "= *", tree->left->left->var, "\n\0"};
				setCode(tree->left, combineStrings(newCode, 6));*/
				
				setVar(tree, tree->left->var);
				char* newCode2 [] = {tree->left->code, tree->right->left->code,"\t*(",tree->var, ")=", tree->right->left->var, "\n\0"};
				setCode(tree, combineStrings(newCode2, 7));
			}
			else{
				char* newCode [] = {tree->right->left->code,"\t",tree->var, "=", tree->right->left->var, "\n\0"};
				setCode(tree, combineStrings(newCode, 6));
			}
		}
	}
	if (!strcmp(tree->token,"+") ||!strcmp(tree->token,"<") ||!strcmp(tree->token,">")||!strcmp(tree->token,"<=")||!strcmp(tree->token,">=") ||!strcmp(tree->token,"==")||!strcmp(tree->token,"!=")||!strcmp(tree->token,"-") || !strcmp(tree->token,"*") || !strcmp(tree->token,"/")){
		setVar(tree, freshVar());
		
		char* newCode [] = {tree->left->code, tree->right->code,"\t", tree->var, "=", tree->left->var, tree->token, tree->right->var, "\n\0"};
		setCode(tree, combineStrings(newCode, 9));
	}
	if(!strcmp(tree->token,"NEGATIVE")){
		setVar(tree, freshVar());
		char* newCode [] = {tree->left->code,"\t", tree->var, "=", "-", tree->left->var, "\n\0"};
		setCode(tree, combineStrings(newCode, 7));
	}
	if(!strcmp(tree->token,"ADDRESS")){
		setVar(tree, freshVar());
		char* newCode [] = {tree->left->code,"\t", tree->var, "=", "&", tree->left->var, "\n\0"};
		setCode(tree, combineStrings(newCode, 7));
	}
	if(!strcmp(tree->token,"POINTER")){
		if(tree->right != NULL){
			setVar(tree, freshVar());
			char* newCode [] = {tree->right->code, tree->left->code,"\t*(", tree->left->var, ")=", tree->right->var, "\n\0"};
			setCode(tree, combineStrings(newCode, 7));
		}
		else{
			setVar(tree, freshVar());
			char* newCode [] = {tree->left->code,"\t", tree->var, "=", "*", tree->left->var, "\n\0"};
			setCode(tree, combineStrings(newCode, 7));
		}
	}
	if(!strcmp(tree->token,"STRING")){
		if(!strcmp(tree->right->left->token, ",")){
			node* temp = tree->right->left;
			while(temp->right != NULL && strcmp(temp->right->token, "EMPTY"))
				temp = temp->right;
			setVar(tree->left, temp->left->token);
			char* newCode2 [] = {"\t",tree->left->var, "=", tree->right->right->left->var, "\n\0"};
			setCode(tree, combineStrings(newCode2, 5));
		}
		else{
			setVar(tree->left, tree->left->token);
			char* newCode2 [] = {"\t",tree->left->var, "=", tree->right->right->left->var, "\n\0"};
			setCode(tree, combineStrings(newCode2, 5));
		}
		
	}
	if(tree->left != NULL && !strcmp(tree->left->token,"=")){
		setVar(tree, tree->token);
		if(!strcmp(tree->left->left->token,"||") || !strcmp(tree->left->left->token,"&&")){
			char * trueL = (char*)malloc(1);
			strcpy(trueL,freshLabel());
			char * falseL = (char*)malloc(1);
			strcpy(falseL,freshLabel());
			char * restL = (char*)malloc(1);
			strcpy(restL,freshLabel());
			char* newCode [] = {shortCircuit(tree->left->left,trueL,falseL),"\n",trueL,":\t",tree->var, "=1\n\tgoto ",restL, "\n", falseL,":\t",tree->var, "=0\n", restL, ":"};
			setCode(tree, combineStrings(newCode,14));
		}
		else{
			char* newCode [] = {tree->left->left->code,"\t", tree->var, "=", tree->left->left->var, "\n\0"};
			setCode(tree, combineStrings(newCode, 6));
			if(tree->left->right != NULL){
				char* newCode1 [] = {tree->code, tree->left->right->code};
				setCode(tree, combineStrings(newCode1, 2));
				}
		}
	}
	if(!strcmp(tree->token,"FUNC")){
		int pop = argsPop(tree->right);
		char* num = (char*) malloc(1);
		sprintf(num,"%d", pop);
		setVar(tree, freshVar());
		char* newCode [] = {tree->right->code,"\t", tree->var," = LCall ",tree->left->var,"\n\t","PopParams ",num,"\n"};
		setCode(tree, combineStrings(newCode, 9));
	}
	if(!strcmp(tree->token,"RET")){
		char* newCode [] = {tree->left->code,"\t","Return ",tree->left->var,"\n"};
		setCode(tree, combineStrings(newCode,5));
	}
	 if (!strcmp(tree->token,"IF")){
		char * trueL = (char*)malloc(1);
		strcpy(trueL,freshLabel());
		char * falseL = (char*)malloc(1);
		strcpy(falseL,freshLabel());
		char* newCode [] = {shortCircuit(tree->left,trueL,falseL),"\n",trueL,":",tree->right->left->code};
		setCode(tree, combineStrings(newCode,5));	
		if(tree->right->right != NULL && !strcmp(tree->right->right->token,"ELSE")){
			char * elseL = (char*)malloc(1);
			strcpy(elseL,freshLabel());
			char* newCode [] = {tree->code,"\tgoto ", elseL,"\n",falseL, ": ", tree->right->right->code, elseL, ":"};
			setCode(tree, combineStrings(newCode,9));
		}
		else{
			char* newCode [] = {tree->code, falseL, ": "};
			setCode(tree, combineStrings(newCode,3));
		}
	}
	if (!strcmp(tree->token,"WHILE")){
		char * begin = (char*)malloc(1);
		strcpy(begin,freshLabel());
		char * after = (char*)malloc(1);
		strcpy(after,freshLabel());
			char * restL = (char*)malloc(1);
			strcpy(restL,freshLabel());
			char* newCode [] = {begin,":", shortCircuit(tree->left,restL,after),"\n",restL, ":",tree->right->code,"\tgoto ",begin,"\n",after,":"};
			setCode(tree, combineStrings(newCode,12));	
	}
	if(!strcmp(tree->token,"INT FUNC") || !strcmp(tree->token,"VOID FUNC")|| !strcmp(tree->token,"REAL FUNC") || !strcmp(tree->token,"CHAR FUNC") || !strcmp(tree->token,"BOOL FUNC") || !strcmp(tree->token,"INT* FUNC") || !strcmp(tree->token,"REAL* FUNC")|| !strcmp(tree->token,"CHAR* FUNC")){
		char* newCode [] = {tree->left->var,":\n","\tBegin Func\n", tree->right->code,"\tEndFunc\n"};
		setCode(tree, combineStrings(newCode,5));
	}
	if(!strcmp(tree->token,"ARGS")){
		char* newCode [] = {tree->left->code, "\tpushParam ", tree->left->var, "\n"};
		setCode(tree, combineStrings(newCode, 4));
		setVar(tree, tree->left->var);
		if (tree->right!=NULL && strcmp(tree->right->token,"EMPTY")){
			char* newCode [] = {tree->code,tree->right->code};
			setCode(tree, combineStrings(newCode, 2));
		}
	}
	if(!strcmp(tree->token,"MOREARGS")){
		char* newCode [] = {tree->left->code, "\tpushParam ", tree->left->var, "\n"};
		setCode(tree, combineStrings(newCode, 4));
		if (tree->right!=NULL && strcmp(tree->right->token,"EMPTY")){
			char* newCode [] = {tree->code,tree->right->code};
			setCode(tree, combineStrings(newCode, 2));
		}
	}
	if(!strcmp(tree->token,"CODE")){
		FILE *fp;
		fp = fopen("3AD Code.txt", "w");
		fprintf(fp, "%s", tree->code);
	}
		
	
}

int argsPop(node* tree){
	if(tree == NULL)
		return 0;
	if(!strcmp(tree->token,"REALVAL")) return 8;
	if(!strcmp(tree->token,"CHARVAL")) return 1;
	if(!strcmp(tree->token,"INTNUM") || !strcmp(tree->token,"CHARPV") || !strcmp(tree->token,"INTPV") || !strcmp(tree->token,"REALPV")|| !strcmp(tree->token,"VARNAMEVAL")) return 4;
	return argsPop(tree->left) + argsPop(tree->right);
	
}

char* shortCircuit(node* tree,char* trueL,char* falseL){
	if (!strcmp(tree->left->token,"NOT")){
		char* newCode [] = {shortCircuit(tree->left->left, falseL, trueL)};
		return combineStrings(newCode,1);
	}
	if (strcmp(tree->token,"&&") && strcmp(tree->token,"||")){
		if(tree->left->left != NULL && !strcmp(tree->left->left->token,"true")){
			char* newCode [] = {tree->code, "\tgoto ", trueL};
			return combineStrings(newCode,3);
		}
		else if(tree->left->left != NULL && !strcmp(tree->left->left->token,"false")){
			char* newCode [] = {tree->code, "\tgoto ", falseL};
			return combineStrings(newCode,3);
		}
		else{
			char* newCode [] = {tree->code,"\tif ", tree->var, " goto ", trueL, "\n\tgoto ", falseL};
			return combineStrings(newCode,7);
		}
	}
	else if (!strcmp(tree->token,"||")){
		char* f =freshLabel();
		char* newCode [] = {shortCircuit(tree->left,trueL, f), "\n", f, ": ", shortCircuit(tree->right,trueL, falseL)};
	return combineStrings(newCode,5);	
	}
	else if (!strcmp(tree->token,"&&")){
		char* t =freshLabel();
		char* newCode [] = {shortCircuit(tree->left,t, falseL), "\n", t, ": ", shortCircuit(tree->right,trueL, falseL)};
	return combineStrings(newCode,5);			
	}
	
}

char* scanTree(list* SymbolTable,node* TotalTree, int flag){
	if(TotalTree->token==NULL)
		return NULL;
	if (!strcmp(TotalTree->token,"FUNC")){
		SymbolTable = addToHead(SymbolTable);
	}
	else if (!strcmp(TotalTree->token,"BLOCK")){
		SymbolTable = addToHead(SymbolTable);
	}
	else if(!strcmp(TotalTree->token,"VARNAMEVAL")){	
		if(scanST(SymbolTable, TotalTree->left->token) == ERRORV){
			char* newCode [] = {TotalTree->left->token," is not defined"};
			return combineStrings(newCode,2);
			
		}
		if(TotalTree->right != NULL && !strcmp(TotalTree->right->token, "ASSIGN")){
			if(TotalTree->left->left != NULL && !strcmp(TotalTree->left->left->token, "[]")){
				if(getType(TotalTree->right->left, SymbolTable)!=CHARV){
					char* newCode [] = {TotalTree->left->token," given semantic error\n"};
					return combineStrings(newCode,2);
				}
			}
			else if(getType(TotalTree->right->left, SymbolTable) != scanST(SymbolTable, TotalTree->left->token) && !(scanST(SymbolTable, TotalTree->left->token) >= CHARPV && scanST(SymbolTable, TotalTree->left->token) <= REALPV && getType(TotalTree->right->left, SymbolTable) == NULLV)){
				char* newCode [] = {TotalTree->left->token," given semantic error\n"};
				return combineStrings(newCode,2);
			}
		}		
	}
	else if(!strcmp(TotalTree->token,"[]")){	
		if(getType(TotalTree->left, SymbolTable) != INTV)
			return "inside [] the value has to be int\n";
	}
	else if(!strcmp(TotalTree->token,"POINTER")){	
		if(getType(TotalTree->left, SymbolTable)<CHARPV || getType(TotalTree->left, SymbolTable) > REALPV){
			return "* can be operate on pointer type only\n";
		}
		else if(TotalTree->right && !strcmp(TotalTree->right->token,"ASSIGN")){
			if(getType(TotalTree, SymbolTable) != getType(TotalTree->right->left, SymbolTable))
			{
				char* newCode [] = {TotalTree->left->left->token," given semantic error\n"};
				return combineStrings(newCode,2);
			}
				
		}
	}
	else if(!strcmp(TotalTree->token,"FUNC")){
		if(getType(TotalTree->left, SymbolTable) < FUNCINTV || getType(TotalTree->left, SymbolTable) > VOIDV)
			return "function call before assigment\n";
		argsL* arguments = getArgs(SymbolTable, TotalTree->left->left->token);
		int size = 0;
		int* callArguments;
		callArguments = funCall(TotalTree->right, SymbolTable, callArguments,&size);
		if(size != arguments->size)
			return "arguments number don't match\n";
		else{
			for(int i=0;i<size;i++){
				if(callArguments[i] != arguments->args[i]){
					if(callArguments[i] == ERRORV)
						return "argument pass to function before decleration\n";
					return "arguments types don't match\n";
				}
			}
		}		
			
		
	}
	else if(!strcmp(TotalTree->token,"IF")){	
		if(getType(TotalTree->left, SymbolTable) != BOOLV)
			return "inside if has to be boolean expression";
	}
	else if(!strcmp(TotalTree->token,"WHILE")){	
		if(getType(TotalTree->left, SymbolTable) != BOOLV)
			return "inside while has to be boolean expression";
	}
	else if(!strcmp(TotalTree->token,"INT")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, INTV,TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
				return combineStrings(newCode,2);
		}
			
	}
	else if(!strcmp(TotalTree->token,"CHAR")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, CHARV,TotalTree->left->token);
		else
		{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
			
	}
	else if(!strcmp(TotalTree->token,"REAL")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, REALV,TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"STRING")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, STRINGV,TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"BOOL")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, BOOLV,TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"INT*")){
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, INTPV,TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"CHAR*")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, CHARPV,TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"REAL*")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, REALPV,TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"VOID FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){
			addVar(SymbolTable, VOIDV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"INT FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){
			addVar(SymbolTable, FUNCINTV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"CHAR FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){			
			addVar(SymbolTable, FUNCCHARV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"REAL FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){
			addVar(SymbolTable, FUNCREALV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"BOOL FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){
			addVar(SymbolTable, FUNCBOOLV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"INT* FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){
			addVar(SymbolTable, FUNCINTPV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"CHAR* FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){
			addVar(SymbolTable, FUNCCHARPV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"REAL* FUNC")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV){
			addVar(SymbolTable, FUNCREALPV,TotalTree->left->token);
			functionArgs(TotalTree->right->left, SymbolTable, 0);
			switch (checkMain(SymbolTable,TotalTree))
			{
				case 1:	return "main already defined\n";
				case 2:	return"main function can't get arguments\n";
			}
		}
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,",")){	
		if(scanHead(SymbolTable, TotalTree->left->token) == ERRORV)
			addVar(SymbolTable, SymbolTable->type[SymbolTable->size-1],TotalTree->left->token);
		else{
			char* newCode [] = {TotalTree->left->token," already defined"};
			return combineStrings(newCode,2);
		}
	}
	else if(!strcmp(TotalTree->token,"=")){
		int typeS = getType(TotalTree->left, SymbolTable);
		if(!(SymbolTable->type[SymbolTable->size-1] >= CHARPV && SymbolTable->type[SymbolTable->size-1] <= REALPV && typeS == NULLV) && SymbolTable->type[SymbolTable->size-1] != typeS){
			char* newCode [] = {SymbolTable->varName[SymbolTable->size-1]," given semantic error\n"};
			return combineStrings(newCode,2);
		}
			
	}
	if(TotalTree->left){
		char* result = scanTree(SymbolTable, TotalTree->left, flag);
		if(result !=NULL)
			return result;
	}
	if(TotalTree->right){
		char* result = scanTree(SymbolTable, TotalTree->right, flag);
		if(result !=NULL)
			return result;
	}
	if (TotalTree->token && (!strcmp(TotalTree->token,"BLOCK")||!strcmp(TotalTree->token,"BODY")) )
	{
		if (!strcmp(TotalTree->token,"BODY") && SymbolTable->next != NULL 						         && SymbolTable->next->type[SymbolTable->next->size-1]>=FUNCINTV 					&&SymbolTable->next->type[SymbolTable->next->size-1] <= VOIDV){
			int funcType = SymbolTable->next->type[SymbolTable->next->size-1];
			int numOfReturns=0;			
			switch(funcType){
				case FUNCCHARV:{	
					if(!checkFuncType(TotalTree, CHARV,SymbolTable,&numOfReturns) || numOfReturns == 0){
						return "return type not match function type\n";
					}
					break;
				}
				case FUNCINTV:{	
					if(!checkFuncType(TotalTree, INTV,SymbolTable,&numOfReturns)|| numOfReturns == 0){
						return "return type not match function type\n";
					}
					break;
				}
				case FUNCREALV:{	
					if(!checkFuncType(TotalTree, REALV,SymbolTable,&numOfReturns)|| numOfReturns == 0){
						return "return type not match function type\n";
					}
					break;
				}
				case FUNCBOOLV:{	
					if(!checkFuncType(TotalTree, BOOLV,SymbolTable,&numOfReturns)|| numOfReturns == 0){
						return "return type not match function type\n";
					}
					break;
				}
				case FUNCINTPV:{	
					if(!checkFuncType(TotalTree, INTPV,SymbolTable,&numOfReturns) || numOfReturns == 0){
						return "return type not match function type\n";
					}
					break;
				}
				case FUNCREALPV:{	
					if(!checkFuncType(TotalTree, REALPV,SymbolTable,&numOfReturns)|| numOfReturns == 0){
						return "return type not match function type\n";
					}
					break;
				}
				case FUNCCHARPV:{	
					if(!checkFuncType(TotalTree, CHARPV,SymbolTable,&numOfReturns) || numOfReturns == 0 ){
						return "return type not match function type\n";
					}
					break;
				}
				case VOIDV:{	
					if(!checkFuncType(TotalTree, NULLV,SymbolTable,&numOfReturns)){
						return "return type not match function type\n";
					}
					break;
				}
			}
			

		}
		SymbolTable = deleteHead(SymbolTable);	
	}
	return NULL;
	
}
int checkMain(list* ST,node* Tree)
{
	if (!strcmp(Tree->left->token,"main")){
		mainCount+=1;
		if (mainCount>1)
			return 1;
		if (ST->argsType[ST->size-1].size != 0)
			return 2;
	}
	return 0;	
}

			
int checkFuncType(node* subTree, int type, list* SymbolTable, int* num){
	if(subTree == NULL){
		return 1;
	}
	int response=1;
	if(subTree->right != NULL && (!strcmp(subTree->right->token, "INT FUNC") || !strcmp(subTree->right->token, "REAL FUNC") || !strcmp(subTree->right->token, "CHAR FUNC") || !strcmp(subTree->right->token, "BOOL FUNC") || !strcmp(subTree->right->token, "STRING FUNC") || !strcmp(subTree->right->token, "INT* FUNC") || !strcmp(subTree->right->token, "VOID FUNC")|| !strcmp(subTree->right->token, "REAL* FUNC") || !strcmp(subTree->right->token, "CHAR* FUNC"))){

		response *= checkFuncType(subTree->left, type, SymbolTable,num);
	}
	else if(!strcmp(subTree->token, "RET")){
		if(getType(subTree->left, SymbolTable) != type)
			{	
				
				return 0;
			}
		*num=1;
	}
	
	else {
		if(subTree->right != NULL)
			response *= checkFuncType(subTree->right, type, SymbolTable,num);
		if(subTree->left != NULL)
			response *= checkFuncType(subTree->left, type, SymbolTable,num);
	}
	return response; 
}



int* funCall(node* head, list* ST, int* types, int* size){
	if(head == NULL)
		return types;	
	if(!strcmp(head->token, "ARGS") || !strcmp(head->token, "MOREARGS")){
		if(*size == 0)
			types = (int*)malloc(sizeof(int)*(++(*size)));
		else
			types = (int*)realloc(types,sizeof(int)*(++(*size)));
		types[*size-1] = getType(head->left, ST);
	}
	funCall(head->right, ST, types, size);
}

void functionArgs(node* temp,list* SymbolTable, int type){
	if(temp != NULL){
		if(!strcmp(temp->token,"INT")){
			type = INTV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,"REAL")){
			type = REALV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,"STRING")){
			type = STRINGV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,"BOOL")){
			type = BOOLV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,"CHAR")){
			type = CHARV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,"INT*")){
			type = INTPV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,"REAL*")){
			type = REALPV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,"CHAR*")){
			type = CHARPV;
			addArg(SymbolTable, type);
		}
		else if (!strcmp(temp->token,",")){
			addArg(SymbolTable, type);
		}
		functionArgs(temp->left,SymbolTable, type);
		functionArgs(temp->right,SymbolTable, type);
	}
}

int getType(node* subTree, list* ST){
	if(!strcmp(subTree->token,"INTNUM")){
		return INTV;
	}
	else if(!strcmp(subTree->token,"REALVAL")){
		return REALV;
	}
	else if(!strcmp(subTree->token,"CHARVAL")){
		return CHARV;
	}
	else if(!strcmp(subTree->token,"STRINGVAL")){
		return STRINGV;
	}
	else if(!strcmp(subTree->token,"BOOLVAL")){
		return BOOLV;
	}
	else if(!strcmp(subTree->token,"NULL")){
		return NULLV;
	}
	else if(!strcmp(subTree->token,"FUNC")){
		int typeF = getType(subTree->left, ST);
			switch(typeF){
				case FUNCINTV: return INTV;
				case FUNCREALV: return REALV;
				case FUNCCHARV: return CHARV;
				case FUNCBOOLV: return BOOLV;
				case FUNCINTPV: return INTPV;
				case FUNCREALPV: return REALPV;
				case FUNCCHARPV: return CHARPV;
				default: return ERRORV;
			}
		
	}
	else if(!strcmp(subTree->token,"POINTER")){
		if(subTree->left != NULL && strcmp(subTree->left->token, "VARNAMEVAL") && strcmp(subTree->left->token, "+") && strcmp(subTree->left->token, "-") && strcmp(subTree->left->token, "*"))
			return ERRORV;
		int typeL = getType(subTree->left,ST);
		if (typeL == INTPV)
			return INTV;
		else if(typeL == REALPV)
			return REALV;
		else if(typeL == CHARPV)
			return CHARV;
		else
			return ERRORV;
		
	}
	else if(!strcmp(subTree->token,"VARNAMEVAL")){
		if(subTree->right != NULL && !strcmp(subTree->right->token, "[]")){
			if (scanST(ST, subTree->left->token) != ERRORV)
				return CHARV;
		}
		return scanST(ST, subTree->left->token);
	}
	else if(!strcmp(subTree->token,"+") || !strcmp(subTree->token,"-") || !strcmp(subTree->token,"*") || !strcmp(subTree->token,"/")){
		int typeR = getType(subTree->right,ST);
		int typeL= getType(subTree->left, ST);
		if(typeR == typeL && typeL == INTV)
			return INTV;
		else if ((typeR == REALV || typeR == INTV) && (typeL == REALV || typeL == INTV))
			return REALV;
		else if ((typeL == CHARPV && typeR == INTV)||(typeL == INTV && typeR == CHARPV))
			return CHARPV;
		else if ((typeL == INTPV && typeR == INTV)||(typeL == INTV && typeR == INTPV))
			return INTPV;
		else if ((typeL == REALPV && typeR == INTV)||(typeL == INTV && typeR == REALPV))
			return REALPV;
		else
			return ERRORV;
	}
	else if(!strcmp(subTree->token,">") || !strcmp(subTree->token,"<") || !strcmp(subTree->token,">=") || !strcmp(subTree->token,"<=")){
		int typeR = getType(subTree->right,ST);
		int typeL= getType(subTree->left, ST);
		if ((typeR == REALV || typeR == INTV) && (typeL == REALV || typeL == INTV))
			return BOOLV;
		else
			return ERRORV;
	}
	else if(!strcmp(subTree->token,"||") || !strcmp(subTree->token,"&&")){
		int typeR = getType(subTree->right,ST);
		int typeL= getType(subTree->left, ST);
		if (typeL == BOOLV && typeR == BOOLV)
			return BOOLV;
		else
			return ERRORV;
	}
	else if(!strcmp(subTree->token,"!=") || !strcmp(subTree->token,"==")){
		int typeR = getType(subTree->right,ST);
		int typeL= getType(subTree->left, ST);
		if (typeL == typeR && typeL >= INTV && typeL <= REALPV && typeL != STRINGV)
			return BOOLV;
		else
			return ERRORV;
	}
	else if(!strcmp(subTree->token,"LEN")){
		int typeL= getType(subTree->left, ST);
		if (typeL == STRINGV)
			return INTV;
		else
			return ERRORV;
	}
	else if(!strcmp(subTree->token,"ADDRESS")){
		int typeL= getType(subTree->left, ST);
		switch (typeL){
			case INTV: return INTPV;
			case REALV: return REALPV;
			case STRINGV: {if(subTree->right != NULL && !strcmp(subTree->right->token,"[]"))			
						return CHARPV;
					}
			break;
			case CHARV: return CHARPV;
			default: return ERRORV;
			break;
		}
	}
	else if(!strcmp(subTree->token,"NOT")){
		int typeL= getType(subTree->left, ST);
		if (typeL == BOOLV)
			return BOOLV;
		else
			return ERRORV;
	}
	else if(!strcmp(subTree->token,"NULL"))
		return NULLV;
	else if (subTree->left != NULL)
		return getType(subTree->left, ST);
	else
		return ERRORV;
}


int yyerror(const char* msg){
	printf("At line: %d , At token: '%s'. \nError Message : %s\n", yylineno,yytext,msg);
	errorA = 1;
	return 0;
}
/*
void freeTree(node* TotalTree){
	if(TotalTree->left == NULL && TotalTree->right == NULL){
		if(TotalTree->token != NULL)
			free(TotalTree->token);
		free(TotalTree);
	}
	else if(TotalTree->left != NULL)
		freeTree(TotalTree->left);
	else if(TotalTree->right != NULL)
		freeTree(TotalTree->right);
		
}
*/
int yywrap(){return 1;}

node *mknode(char *token,node *left,node *right)
{
	
	node *newnode = (node*)malloc(sizeof(node));
	char *newstr = (char*)malloc(sizeof(token)+1);
	//newnode->bytes =0;	
	strcpy(newstr,token);
	newnode->left=left;
	newnode->right=right;
	newnode->token=newstr;
	newnode->var = "";
	newnode->code = "";
	newnode->trueLabel = "";
	newnode->falseLabel = "";
	return newnode;
}


void printtree(node *tree, int depth)
{
	if(!strcmp(tree->token,"CHARVAL") ||!strcmp(tree->token,"INTNUM") || !strcmp(tree->token,"REALVAL")||!strcmp(tree->token,"VARNAMEVAL") || !strcmp(tree->token,"STRINGVAL")|| !strcmp(tree->token,"MOREARGS")){
		printtree(tree->left, depth);
	}
	if(!strcmp(tree->token,"BLOCK1")){
		printtree(tree->right, depth);
	}
	else{
		if(!strcmp(tree->token,"EMPTY"))
			return;
		int hasSon = (tree->left || tree->right);
		for(int i=0;i<depth;i++)
			printf("  ");
		if(strcmp(tree->token, "VARNAMEVAL") 
				&& strcmp(tree->token, "CHARVAL") 
				&& strcmp(tree->token, "INTNUM") 
				&& strcmp(tree->token, "REALVAL") 
				&& strcmp(tree->token, "STRINGVAL") 
			){

		if(!hasSon)
			if
				(!strcmp(tree->token, "INT FUNC") 
				|| !strcmp(tree->token, "REAL FUNC") 
				|| !strcmp(tree->token, "CHAR FUNC") 
				|| !strcmp(tree->token, "BOOL FUNC") 
				|| !strcmp(tree->token, "STRING FUNC") 
				|| !strcmp(tree->token, "INT* FUNC") 
				|| !strcmp(tree->token, "VOID FUNC")
				|| !strcmp(tree->token, "REAL* FUNC") 
				|| !strcmp(tree->token, "CHAR* FUNC")
				)
			{
				printf("(%s","FUNC");
			}else{
				printf("(%s",tree->token);
			}
		else{
			if
				(!strcmp(tree->token, "INT FUNC") 
				|| !strcmp(tree->token, "REAL FUNC") 
				|| !strcmp(tree->token, "CHAR FUNC") 
				|| !strcmp(tree->token, "BOOL FUNC") 
				|| !strcmp(tree->token, "STRING FUNC") 
				|| !strcmp(tree->token, "INT* FUNC") 
				|| !strcmp(tree->token, "VOID FUNC")
				|| !strcmp(tree->token, "REAL* FUNC") 
				|| !strcmp(tree->token, "CHAR* FUNC")
				)
			{
				printf("(%s\n","FUNC");
			}else{
				printf("(%s\n",tree->token);
			}

			}
		}else{
				printf("(\n");
		}
		if(tree->left){
			printtree(tree->left, depth+1);
		}
		if(tree->right){
			printtree(tree->right,depth+1);
		}
		if(hasSon){
			for(int i=0;i<depth;i++)
				printf("  ");
		}
		printf(")\n");
	}
}





int scanHead(list* head, char* varN){
	for (int i=0;i<head->size;i++){
		if(!strcmp(head->varName[i], varN)){
			return head->type[i];
		}
	}
	return ERRORV;
}

int scanST(list* head,char* varN){
	list* node = head;
	while(node != NULL){
		for (int i=0;i<node->size;i++){
			if(!strcmp(node->varName[i], varN)){
				return node->type[i];
			}
		}
		node = node->next;
	}
	return ERRORV;
}

argsL* getArgs(list* head, char* varN){
	list* node = head;
	while(node != NULL){
		for (int i=0;i<node->size;i++){
			if(!strcmp(node->varName[i], varN)){
				return &node->argsType[i];
			}
		}
		node = node->next;
	}
	return NULL;
}







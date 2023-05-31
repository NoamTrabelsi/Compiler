#define _CRT_SECURE_NO_WARNINGS
#include<stdio.h>
#include<stdlib.h>
#include<string.h>

#define SWAP(x,y,t)((t)=(x),(x)=(y),(y)=(t))

typedef struct argsL argsL;
struct argsL {
	int size;
	int* args;
};

typedef struct List list;
struct List {
	int size;
	int* type;
	char** varName;
	argsL* argsType;
	list* next;
	list* previous;
};

void addArg(list* node, int type);
list* BuildNode();
list* addToHead(list*);
list* FreeList(list*);
void addVar(list*, int,char*);
list* deleteHead(list*);

list* BuildNode(){
	list *node = (list*)malloc(sizeof(list));
	node->argsType = NULL;
	node->type = NULL;
	node->varName = NULL;
	node->size=0;
	node->next = NULL;
	return node;
}

list* addToHead(list* head){
	list *new_elem = BuildNode();
	new_elem->next = head;
	return new_elem;
}

list* FreeList(list *head){
	list *temp;
	while (head != NULL)
	{
		temp = head;
		head = head->next;
		if(temp->type != NULL)
			free(temp->type);
		if(temp->varName != NULL){
			for(int i =0;i<temp->size;i++)
				free(temp->varName[i]);
			free(temp->varName);
		}
		if(temp->argsType != NULL){
			for(int i =0;i<temp->size;i++)
				free(temp->argsType[i].args);
			free(temp->argsType);
		}
		free(temp);
	}
	return NULL;
}

list* deleteHead(list *head){
	list* temp = head;
	head = head->next;
	temp->next = NULL;
	FreeList(temp);
	return head;
}


void addVar(list* node, int type,char* varname1){
	if(!(node->size && node->size)){
		node->type = (int*)malloc(sizeof(int)*(++node->size));
		node->varName = (char**)malloc(sizeof(char*)*(node->size));
		node->argsType = (argsL*)malloc(sizeof(argsL)*(node->size));
	}
	else{
		node->type = (int*)realloc(node->type, sizeof(int)*(++node->size));
		node->varName = (char**)realloc(node->varName, sizeof(char*)*(node->size));
		node->argsType = (argsL*)realloc(node->argsType, sizeof(argsL)*(node->size));
	}
	node->type[node->size-1] = type;
	node->argsType[node->size-1].size=0;
	node->argsType[node->size-1].args = NULL;
	node->varName[node->size-1] = (char*) malloc(1);
	strcpy(node->varName[node->size-1],varname1);
}

void addArg(list* node, int type){
	int tempSize;
	if(node->argsType[node->size-1].size == 0){
		tempSize = ++(node->argsType[node->size-1].size);
		node->argsType[node->size-1].args = (int*)malloc(sizeof(int)*(tempSize));	
	}
	else{
		tempSize = ++(node->argsType[node->size-1].size);
		node->argsType[node->size-1].args = (int*)realloc(node->argsType[node->size-1].args ,sizeof(int)*(tempSize));
	}
	node->argsType[node->size-1].args[tempSize-1] = type;
}
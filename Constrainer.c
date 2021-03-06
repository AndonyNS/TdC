/****************************************************************
              Copyright (C) 1986 by Manuel E. Bermudez
              Translated to C - 1991
*****************************************************************/

#include <stdio.h>
#include <header/Open_File.h>
#include <header/CommandLine.h>
#include <header/Table.h>
#include <header/Text.h>
#include <header/Error.h>
#include <header/String_Input.h> 
#include <header/Tree.h>
#include <header/Dcln.h>
#include <header/Constrainer.h>

#define ProgramNode    1
#define TypesNode      2
#define TypeNode       3
#define DclnsNode      4
#define VarNode        5
#define IntegerTNode   6
#define BooleanTNode   7
#define BlockNode      8
#define AssignNode     9
#define OutputNode     10
#define IfNode         11
#define WhileNode      12
#define NullNode       13

#define GTNode         14
#define LTNode         15
#define GTENode        16
#define NENode         17
#define EQNode         18
#define LTENode        19

#define PlusNode       20
#define MinusNode      21

#define ORNode         22
#define MODNode        23
#define ANDNode        24
#define MultiplyNode   25
#define DivisionNode   26

#define NOTNode        27
#define UMinusNode     28
#define POWNode        29

#define ReadNode       30
#define EofNode        31
#define TrueNode       32
#define FalseNode      33
#define IntegerNode    34
#define IdentifierNode 35

#define RepeatNode     36
#define LoopNode       37
#define ExitNode       38
#define SwapNode       39
#define UptoNode       40
#define DownToNode     41
#define CaseNode       42
#define CaseClauseNode 43
#define RangeNode      44
#define OtherwiseNode  45

#define CharacterTNode 46
#define CharacterNode  47
#define ConstsNode     48
#define ConstNode      49
#define LitNode        50
#define SuccNode       51
#define PredNode       52
#define ChrNode        53
#define OrdNode        54
#define StringNode     55

#define NumberOfNodes  55

typedef TreeNode UserType;

/****************************************************************
 Add new node names to the end of the array, keeping in strict
  order with the define statements above, then adjust the i loop
  control variable in InitializeConstrainer().
*****************************************************************/
char *node[] = { "program", "types", "type", "dclns",
                 "var", "integer", "boolean", "block",
                 "assign", "output", "if", "while", 
                 "<null>", ">", "<", ">=",
		           "<>", "=", "<=", "+",
            	  "-", "or", "mod", "and",
                 "*", "/", "not", "neg",
                 "pow", "read", "eof", "true", "false",
		           "<integer>", "<identifier>","repeat", 
                 "loop", "exit", "<swap>", "<upto>",
                 "<downto>", "case", "<case_clause>",
                 "<range>", "<otherwise>", "char", "<char>",
                 "<consts>", "const", "lit", "succ",
                 "pred", "chr", "ord", "<string>"
                };


UserType TypeInteger, TypeBoolean, TypeCharacter;
boolean TraceSpecified;
FILE *TraceFile;
char *TraceFileName;
int NumberTreesRead, index;


TreeNode GetMode(TreeNode);
void CheckModeForAssignmentIdentifier(TreeNode);
void IngresarContexto(TreeNode);

void Constrain(void)    
{
   int i;
   InitializeDeclarationTable();
   Tree_File = Open_File("_TREE", "r"); 
   NumberTreesRead = Read_Trees();
   fclose (Tree_File);                     

   AddIntrinsics();

#if 0
   printf("CURRENT TREE\n");
   for (i=1;i<=SizeOf(Tree);i++)
      printf("%2d: %d\n",i,Element(Tree,i));
#endif

   ProcessNode(RootOfTree(1)); 

    
   Tree_File = fopen("_TREE", "w");  
   Write_Trees();
   fclose (Tree_File);                   

   if (TraceSpecified)
      fclose(TraceFile);    
}


void InitializeConstrainer (int argc, char *argv[])
{          
   int i, j;

   InitializeTextModule();
   InitializeTreeModule();

   for (i=0, j=1; i<NumberOfNodes; i++, j++)
      String_Array_To_String_Constant (node[i], j); 
 
   index = System_Flag ("-trace", argc, argv);
 
   if (index)                                       
   {
      TraceSpecified = true; 
      TraceFileName = System_Argument ("-trace", "_TRACE", argc, argv);
      TraceFile = Open_File(TraceFileName, "w");
   }
   else
      TraceSpecified = false;          
}                        

#define GetTypesTree TypesTree = Child (RootOfTree(1), 2); /*typesnode*/

void AddIntrinsics (void)
{
  TreeNode LitTree, TypesTree, TypeBoolTree, TypeIntTree, TypeCharTree;

   AddTree (TypesNode, RootOfTree(1), 2);
 
   /*booleano*/
   TypesTree = Child (RootOfTree(1), 2);
   AddTree (TypeNode, TypesTree, 1);
   TypesTree = Child (RootOfTree(1), 2);
   TypeBoolTree = Child(Child (RootOfTree(1), 2), 1);
   AddTree(IdentifierNode, TypeBoolTree, 1);
   TypeBoolTree = Child(Child (RootOfTree(1), 2), 1);
   AddTree(BooleanTNode, Child(TypeBoolTree, 1), 1);
   TypeBoolTree = Child(Child (RootOfTree(1), 2), 1);
   
   /*Parte derecha del arbol booleano (Lit)*/
   AddTree(LitNode, TypeBoolTree, 2);
   TypeBoolTree = Child(Child (RootOfTree(1), 2), 1);

   /*HIjo izquierdo, "false"*/
   LitTree = Child(Child(Child (RootOfTree(1), 2), 1), 2);
   AddTree(IdentifierNode, LitTree, 1);
   LitTree = Child(Child(Child (RootOfTree(1), 2), 1), 2);
   AddTree(FalseNode, Child( Child(Child(Child (RootOfTree(1), 2), 1), 2), 1), 1);

   /*Hijo derecho, "true"*/
   LitTree = Child(Child(Child (RootOfTree(1), 2), 1), 2);
   AddTree(IdentifierNode, LitTree, 2);
   LitTree = Child(Child(Child (RootOfTree(1), 2), 1), 2);
   AddTree(TrueNode, Child(LitTree, 2), 1);

   /*integer*/
   TypesTree = Child (RootOfTree(1), 2);
   AddTree (TypeNode, TypesTree, 2);
   TypesTree = Child (RootOfTree(1), 2);
   TypeIntTree = Child(Child (RootOfTree(1), 2), 2);
   AddTree(IdentifierNode, TypeIntTree, 1);
   TypeIntTree = Child(Child (RootOfTree(1), 2), 2);
   AddTree(IntegerTNode, Child(TypeIntTree, 1), 1);

   /*char*/
   TypesTree = Child (RootOfTree(1), 2);
   AddTree (TypeNode, TypesTree, 3);
   TypesTree = Child (RootOfTree(1), 2);
   TypeCharTree = Child(Child (RootOfTree(1), 2), 3);
   AddTree(IdentifierNode, TypeCharTree, 1);
   TypeCharTree = Child(Child (RootOfTree(1), 2), 3);
   AddTree(CharacterTNode, Child(TypeCharTree, 1), 1);


   TypeBoolean = Child(Child (RootOfTree(1), 2),1);
   TypeInteger = Child(Child (RootOfTree(1), 2),2);
   TypeCharacter = Child(Child (RootOfTree(1), 2),3);

}

void PrintHeader(TreeNode T, char * message)
{
   printf (message);
   Write_String (stdout,SourceLocation(T));
   printf (" : ");
   printf ("\n");
}

void ErrorHeader (TreeNode T)
{ 
   PrintHeader(T, "<<< CONSTRAINER ERROR >>> AT ");
}

void WarningHeader (TreeNode T)
{ 
  PrintHeader(T, "<<< CONSTRAINER WARNING >>> AT ");
}

int NKids (TreeNode T)
{
   return (Rank(T));
}



UserType Expression (TreeNode T)
{
   UserType Type1, Type2;
   TreeNode Declaration, Temp1, Temp2, Mode, Mode1, Mode2;
   int NodeCount;

   if (TraceSpecified)
   {
      fprintf (TraceFile, "<<< CONSTRAINER >>> : Expn Processor Node ");
      Write_String (TraceFile, NodeName(T));
      fprintf (TraceFile, "\n");
   }
     
   switch (NodeName(T))
   {
      case LTENode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '<=' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case EQNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '=' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeBoolean);
      
      case GTENode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '>=' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case NENode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '<>' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case LTNode :    
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '<' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case GTNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '>' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case NOTNode :
         Type1 = Expression (Child(T,1));
         if (Type1 != TypeBoolean)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENT OF 'not' MUST BE TYPE BOOLEAN\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case ANDNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF 'and' MUST BE THE SAME TYPE\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case ORNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF 'or' MUST BE THE SAME TYPE\n");
            printf ("\n");
         }
         return (TypeBoolean);
	 

      case PlusNode :
      case MinusNode :
      case MODNode :       
      case MultiplyNode :
      case DivisionNode :
      case UMinusNode :
      case POWNode:
         Type1 = Expression (Child(T,1));

         if (Rank(T) == 2)
            Type2 = Expression (Child(T,2));
         else  
            Type2 = TypeInteger;

         if (Type1 != TypeInteger || Type2 != TypeInteger)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '+', '-', 'mod', '*', '/', unary '-', '**' ");
            printf ("MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeInteger);
     
      case EofNode:
         return (TypeBoolean);

      case IntegerNode : 
         return (TypeInteger);

      case CharacterNode:
       return (TypeCharacter);

      case IdentifierNode :
	      Declaration = Lookup (NodeName(Child(T,1)), T);	  
      	Mode = NodeName(Decoration(Child(Declaration, 1)));
	 
         if (Declaration != NullDeclaration){
            Decorate (T, Declaration);
	    
	         if(Mode == TypeNode){
     	      ErrorHeader(T);
	         printf ("CANNOT HAVE A TYPE IN EXPRESSIONS");
	         printf ("\n");
	         }
	         else if(Mode == VarNode){
	            if(Decoration(Declaration) == TypeBoolean)
            		return (TypeBoolean);
	            else if(NodeName(Decoration(Declaration)) == TypeNode && NKids(Decoration(Declaration)) >1  && NodeName(Child(Decoration(Declaration),2) ) == LitNode){
		            return (Decoration(Declaration));
	         }
	         else{
         		return (Decoration(Declaration));
            };
	      }
	      else if(Decoration(Declaration) == TypeBoolean)
		      return (TypeBoolean);
	      else
	         return (Decoration(Declaration));
         }
         else{
	         ErrorHeader(T);
	         printf ("NULL DECLARATION");
   	      printf ("\n");
	      };
   	   return (TypeInteger);

      case RangeNode:
         Type1 = Expression(Child(T,1));
         Type2 = Expression(Child(T,2));
         if(Type1 != Type2){
            ErrorHeader(T);
            printf ("RANGE OPERATOR MUST BE OF SAME TYPE");
            printf ("\n");
         }
         return (Type1);

      case SuccNode:
      	Type1 = Expression(Child(T, 1));
	      Decorate(T, Type1);
      	if(Type1 != TypeInteger && Type1 != TypeCharacter && !(NodeName(Type1) == TypeNode && NKids(Type1)>1 && NodeName(Child(Type1,2)) == LitNode)){
	         ErrorHeader(T);
	         printf ("SUCC WORKS ON INTEGERS/CHARACTER/ENUMERATED EXPRESSIONS.");
	         printf ("\n");
	      };
	      return (Type1);

      case PredNode:
	      Type1 = Expression(Child(T, 1));
	      Decorate(T, Type1);
	      if(Type1 != TypeInteger && Type1 != TypeCharacter && !(NodeName(Type1) == TypeNode && NKids(Type1)>1 && NodeName(Child(Type1,2)) == LitNode)){
	        ErrorHeader(T);
	        printf ("PRED WORKS ON INTEGER/CHARACTER/ENUMERATED EXPRESSIONS.%d", Type1);
	        printf ("\n");
	      };
	      return (Type1);

      case ChrNode:
        Type1 = Expression(Child(T,1));
        Decorate(T, TypeCharacter);
        if(Type1 != TypeInteger){
          ErrorHeader(T);
          printf ("ARGUMENTS OF CHR MUST BE OF TYPE INTEGER.");
	     printf ("\n");
        };
        return (TypeCharacter);

      case OrdNode:
        Type1 = Expression(Child(T,1));
        Decorate(T, TypeInteger);
        if(Type1 != TypeInteger && Type1 != TypeCharacter && !(NodeName(Type1) == TypeNode && NKids(Type1)>1 && NodeName(Child(Type1,2)) == LitNode)){
          ErrorHeader(T);
          printf ("ARGUMENTS OF ORD FUNCTION SHOULD BE OF TYPE LITERAL.");
          printf ("\n");
        };
        return (TypeInteger);
     
      default :
         ErrorHeader(T);
         printf ( "UNKNOWN NODE NAME ");
         Write_String (stdout,NodeName(T));
         printf ("\n");

   }  /* end switch */
}  /* end Expression */




void ProcessNode (TreeNode T) 
{
   int Kid, N;
   String Name1, Name2;
   TreeNode Type1, Type2, Type3, Temp, Dcln1, Mode, Declaration;

   if (TraceSpecified)
   {
      fprintf (TraceFile,
               "<<< CONSTRAINER >>> : Stmt Processor Node ");
      Write_String (TraceFile, NodeName(T));
      fprintf (TraceFile, "\n");
   }

   switch (NodeName(T))
   {
      case ProgramNode : 
         OpenScope();
	 /* for loop context */
	 IngresarContexto(T);
         Name1 = NodeName(Child(Child(T,1),1));
         Name2 = NodeName(Child(Child(T,NKids(T)),1));

         if (Name1 != Name2)
         {
           ErrorHeader(T);
           printf ("PROGAM NAMES DO NOT MATCH\n");
           printf ("\n");
         }

         for (Kid = 2; Kid <= NKids(T)-1; Kid++)
            ProcessNode (Child(T,Kid));
         CloseScope();
         break;
        
      case TypeNode :
	DTEnter (NodeName(Child(Child(T,1), 1)),Child(T, 1),T);
	Decorate(Child(T, 1), T);
	Decorate(Child(Child(T,1), 1), T);
	
	if(NKids(T) > 1){
	  if(NodeName(Child(T, 2)) == LitNode){
	    for(Kid = 1; Kid <= NKids(Child(T, 2)); Kid++){
	      DTEnter (NodeName(Child(Child(Child(T,2), Kid),1)), Child(Child(T, 2), Kid),T);
	      Decorate(Child(Child(Child(T,2),Kid), 1), Child(T, 2));
	      Decorate(Child(Child(T,2), Kid), T);
	    };
	  }
	  else if(NodeName(Child(T,2)) == IdentifierNode){
	      Dcln1 = Lookup(NodeName(Child(Child(T, 2), 1)), T);
	      Decorate(Child(T, 2), Dcln1);	      
	      Decorate(Child(T, 1),Decoration(Dcln1));
	  }
	  else{
	    ErrorHeader(T);
	    printf ("Compiler Error : The second child of TypeNode should be LitNode or Identifier Node.\n");
	    printf("found %d", NodeName(Child(T,2)));
	    printf ("\n");
	  };
	};
         break;

      case TypesNode :
      case ConstsNode:
      case DclnsNode :
         for (Kid = 1; Kid <= NKids(T); Kid++)
            ProcessNode (Child(T,Kid));
         break;


      case VarNode :

	Name1 = NodeName(Child((Child(T, NKids(T))),1));

         Type1 =  Lookup (Name1,T);
	 Decorate(Child(T, NKids(T)) , Type1);
         for (Kid  = 1; Kid < NKids(T); Kid++)
         {
            DTEnter (NodeName(Child(Child(T,Kid),1)), Child(T,Kid), T);
            Decorate (Child(T,Kid), Decoration(Type1));
	    Decorate( Child(Child(T,Kid),1), T);
         };
         break;

   case ConstNode:
     switch(NodeName(Child(T,2))){
     case IntegerNode:
       Name1 = IntegerTNode;
       Type1 =  Lookup (Name1,T);
       break;
     case CharacterNode:
       Name1 = CharacterTNode;
       Type1 =  Lookup (Name1,T);
       break;
     case IdentifierNode:
       Mode = GetMode(Child(T, 2));
       if(Mode != LitNode && Mode != ConstNode){
	 ErrorHeader(T);
	 printf ("CONSTANTS CANNOT BE ASSIGNED A TYPE\n");
	 printf ("\n");
       };
       Type1 = Lookup(NodeName(Child(Child(T, 2), 1)), T);
       Decorate(Child(T, 2), Type1);
       break;
     default:
       printf("Const Node Type Could not be inferred.");
     }
     DTEnter(NodeName(Child(Child(T,1),1)), Child(T,1), T);
     Decorate(Child(T, 1), Decoration(Type1));
     Decorate(Child(Child(T,1),1), T);
     break;

      case BlockNode :
         for (Kid = 1; Kid <= NKids(T); Kid++)
            ProcessNode (Child(T,Kid));
         break;


      case AssignNode :
	 Temp = Lookup("<for_ctxt>", T);
	 while(NodeName(Temp) != ProgramNode)
	   {
	     if(NodeName(Child(Child(Temp, 1), 1)) == NodeName(Child(Child(T, 1), 1)))
	       {
		 ErrorHeader(T);
		 printf ("CANNOT ASSIGN FOR-LOOP VARIABLE\n");
		 printf ("\n");
	       }
	       Temp = Decoration(Temp);
	   };
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

	      CheckModeForAssignmentIdentifier(Child(T, 1));
         if (Type1 != Type2)
         {
            ErrorHeader(T);
            printf ("ASSIGNMENT TYPES DO NOT MATCH\n");
            printf ("\n");
         }
         break;


      case OutputNode :
	for (Kid = 1; Kid <= NKids(T); Kid++){
	  if(NodeName(Child(T, Kid)) != StringNode)
	    Type1 = Expression(Child(T, Kid));  
	  if(NodeName(Child(T,Kid)) == IdentifierNode){
	    Mode = GetMode(Child(T,Kid));
	    if(Mode == LitNode){
	      ErrorHeader(T);
	      printf ("CANNOT OUTPUT ENUMERATED TYPES\n");
	      printf ("\n");
	      continue;
	    };
	  };
	  if (Type1 != TypeInteger && Type1 != TypeCharacter && NodeName(Child(T,Kid)) != StringNode)
	    {
	      ErrorHeader(T);
	      printf ("OUTPUT EXPRESSION MUST BE TYPE INTEGER OR CHARACTER OR STRINGS\n");
	      printf ("\n");
            }
	}
	break;


      case IfNode :
         if (Expression (Child(T,1)) != TypeBoolean)
         {
            ErrorHeader(T);
            printf ("CONTROL EXPRESSION OF 'IF' STMT");
            printf (" IS NOT TYPE BOOLEAN\n");
            printf ("\n");
         } 

         ProcessNode (Child(T,2));
         if (Rank(T) == 3)
            ProcessNode (Child(T,3));
         break;


      case WhileNode :
         if (Expression (Child(T,1)) != TypeBoolean)
         {
            ErrorHeader(T);
            printf ("WHILE EXPRESSION NOT OF TYPE BOOLEAN\n");
            printf ("\n");
         }
         ProcessNode (Child(T,2));
         break;

      case RepeatNode:
         for(Kid = 1; Kid <= NKids(T)-1; Kid++){
          ProcessNode(Child(T,Kid));
         };
         if (Expression (Child(T,NKids(T))) != TypeBoolean)
         {
            ErrorHeader(T);
            printf ("REPEAT EXPRESSION NOT OF TYPE BOOLEAN\n");
            printf ("\n");
         };
	 break;

   case LoopNode:
     OpenScope();
     DTEnter("<loop_ctxt>", T, T);
     for(Kid = 1; Kid <= NKids(T); Kid++){
       ProcessNode(Child(T,Kid));
     };
     CloseScope();
     if(Decoration(T)== 0){
       WarningHeader(T);
       printf("NO 'exit' FROM 'LOOP'.");
       printf("\n");
     }
     break;

   case ExitNode:
     Temp = Lookup("<loop_ctxt>", T);
     if(NodeName(Temp) != LoopNode)
       {
	 ErrorHeader(T);
	 printf("'exit' CAN ONLY BE INSIDE A 'loop' statement");
	 printf("\n");
       }
     else
       {
	 Decorate(T, Temp);
	 Decorate(Temp, T);
       };
     break;

   case SwapNode:
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));
         if (Type1 != Type2 || NodeName(Child(T,1)) != IdentifierNode || NodeName(Child(T,2)) != IdentifierNode)
	   {
            ErrorHeader(T);
            printf ("SWAP TYPES ARE ILLEGAL OR DO NOT MATCH\n");
            printf ("\n");
         }
	 else
	   {
	     CheckModeForAssignmentIdentifier(Child(T,1));
	     CheckModeForAssignmentIdentifier(Child(T,2));

	     Temp = Lookup("<for_ctxt>", T);
	     while(NodeName(Temp) != ProgramNode)
	       {
		 if(NodeName(Child(Child(Temp, 1), 1)) == NodeName(Child(Child(T, 1), 1)))
		   {
		     ErrorHeader(T);
		     printf ("CANNOT SWAP WITH LOOP CONTROL VARIABLE\n");
		     printf ("\n");
		   }
		 Temp = Decoration(Temp);
	       };
	   }
         break;

   case UptoNode:
        Temp = Lookup("<for_ctxt>", T);
	Decorate(T, Temp);
	OpenScope();
	IngresarContexto(T);
	Type1 = Expression(Child(T, 1));
	Type2 = Expression(Child(T, 2));
	Type3 = Expression(Child(T, 3));
	if(Type1 != Type2 || Type2 != Type3)
	  {
	    ErrorHeader(T);
            printf ("FOR LOOP VARIABLE DOESN'T MATCH THE TYPE OF START VALUE");/*, Type1 : %d , Type2: %d, Type3: %d", Type1, Type2, Type3);*/
            printf ("\n");
	  };
	ProcessNode(Child(T, 4));
	while(NodeName(Temp)!= ProgramNode)
	  {
	    if(NodeName(Child(Child(Temp,1), 1)) == NodeName(Child(Child(T, 1),1)))
	      {
		ErrorHeader(T);
		printf ("CANNOT RE-USE A LOOP CONTROL VARIABLE\n");
		printf ("\n");
	      }
	      Temp = Decoration(Temp);
	  };
	CloseScope();
     break;

   case DownToNode:
     Temp = Lookup("<downto_ctxt>", T);
     Decorate(T, Temp);
     OpenScope();
     IngresarContexto(T);
     Type1 = Expression(Child(T, 1));
     Type2 = Expression(Child(T, 2));
     Type3 = Expression(Child(T, 3));
     if(Type1 != Type2 || Type2 != Type3)
	  {
	    ErrorHeader(T);
            printf ("DOWNTO LOOP VARIABLE DOESN'T MATCH THE TYPE OF START VALUE\n");
            printf ("\n");
	  };
	ProcessNode(Child(T, 4));
	while(NodeName(Temp)!= ProgramNode)
	  {
	    if(NodeName(Child(Child(Temp,1), 1)) == NodeName(Child(Child(T, 1),1)))
	      {
		ErrorHeader(T);
		printf ("CANNOT RE-USE A LOOP CONTROL VARIABLE\n");
		printf ("\n");
	      }
	      Temp = Decoration(Temp);
	  };
	CloseScope();
     break;

   case CaseNode:
     Type1 = Expression(Child(T,1));
     for(Kid = 2; Kid <= NKids(T); Kid++){
       if(NodeName(Child(T, Kid)) == CaseClauseNode){
	 Type2 = Expression(Child(Child(T,Kid), 1)); 
	 if(NodeName(Child(Child(T,Kid), 1)) == IdentifierNode){
	   if(NodeName(Decoration(Child(Decoration(Child(Child(T,Kid), 1)),1))) == VarNode){
	     ErrorHeader(Child(Child(T,Kid), 1));
	     printf("CASE CLAUSE CAN ONLY HAVE LIT OR CONST AS LABEL");/*,Type1 %d, Type2 %d", Type1, Type2);*/
	     printf("\n");
	   };
	 };
	 if(Type2 != Type1){
	   ErrorHeader(Child(Child(T,Kid), 1));
	   printf("CASE CLAUSE NOT OF TYPE OF THE CASE EXPRESSION");/*,Type1 %d, Type2 %d", Type1, Type2);*/
	   printf("\n");
	 };

	 ProcessNode(Child(Child(T,Kid), 2)); 
       }
       else if(NodeName(Child(T, Kid)) == OtherwiseNode)
	 {
	   ProcessNode(Child(Child(T,Kid), 1)); 
	 }
     };
     break;

      case ReadNode :	
	for(Kid = 1; Kid <= NKids(T); Kid++){
	  Type1 = Expression(Child(T, Kid));
	  
	  Temp = Lookup("<for_ctxt>", T);
	  while(NodeName(Temp) != ProgramNode)
	    {
	      if(NodeName(Child(Child(Temp, 1), 1)) == NodeName(Child(Child(T, 1), 1)))
		{
		  ErrorHeader(T);
		  printf ("CANNOT READ IN A FOR-LOOP VARIABLE\n");
		  printf ("\n");
		}
	      Temp = Decoration(Temp);
	    };
	  
	  if(Type1 != TypeInteger && Type1 != TypeCharacter)
	    {
	    ErrorHeader(Child(T,Kid));
	    printf("Read STATEMENT ALLOWS INTEGERS AND CHARACTERS TO BE READ");
	    printf("\n");
	  };
	};
	  break;


      case NullNode :  
         break;

      default :
         ErrorHeader(T);
         printf ("UNKNOWN NODE NAME ");
         Write_String (stdout,NodeName(T));
         printf ("\n");

   }  /* end switch */
};  /* end ProcessNode */


void IngresarContexto(TreeNode T)
{
  DTEnter("<for_ctxt>", T);
  DTEnter("<downto_ctxt>", T);
  DTEnter("<loop_ctxt>", T);
};

TreeNode GetMode(T){
  TreeNode Declaration, Mode;
  Declaration = Lookup(NodeName(Child(T, 1)),T);
  Mode = NodeName(Decoration(Child(Declaration,1)));  
  return Mode;
};

void CheckModeForAssignmentIdentifier(TreeNode T){
  TreeNode Declaration, Mode;
  Mode = GetMode(T);
  if(Mode != VarNode){
    ErrorHeader(T);
    printf ("CANNOT ASSIGN/SWAP TYPES, CONSTANTS, LITERALS\n");
    printf ("\n");
  };
};

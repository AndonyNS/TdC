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

#define ProgramNode     1
#define TypesNode       2
#define TypeNode        3
#define DclnsNode       4
#define DclnNode        5
#define IntegerTNode    6
#define BooleanTNode    7
#define BlockNode       8
#define AssignNode      9
#define OutputNode      10
#define IfNode          11
#define WhileNode       12
#define RepeatNode      13
#define LoopNode        14
#define ExitNode        15
#define ForNode         16
#define UptoNode        17
#define DowntoNode      18
#define NullNode        19
#define LENode          20
#define EQNode          21
#define GENode          22
#define NENode          23
#define LTNode          24
#define GTNode          25
#define AndNode         26
#define OrNode          27
#define PlusNode        28
#define MinusNode       29
#define ModNode         30
#define MultNode        31
#define DivNode         32
#define ExpNode         33
#define SwapNode        34
#define NotNode         35
#define ReadNode        36
#define TrueNode        37
#define FalseNode       38
#define EofNode         39
#define IntegerNode     40
#define IdentifierNode  41
#define LOOP_CTXT       42
#define FOR_CTXT        43

#define NumberOfNodes   43

typedef TreeNode UserType;

/****************************************************************
 Add new node names to the end of the array, keeping in strict
  order with the define statements above, then adjust the i loop
  control variable in InitializeConstrainer().
*****************************************************************/
char *node[] = { "program", "types", "type", "dclns",
                 "dcln", "integer", "boolean", "block",
                 "assign", "output", "if", "while", "repeat", "loop", "exit",
                 "for", "to", "downto", "<null>", "<=", "=",">=","<>", 
                 "<", ">", "and","or","+", "-", "mod","*", "/", "**",":=:",
                 "not","read", "true","false", "eof","<integer>", "<identifier>" , "<loop_ctxt>"
                };


UserType TypeInteger, TypeBoolean;
boolean TraceSpecified;
FILE *TraceFile;
char *TraceFileName;
int NumberTreesRead, index;


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


void AddIntrinsics (void)
{
   TreeNode TempTree;

   AddTree (TypesNode, RootOfTree(1), 2);

   TempTree = Child (RootOfTree(1), 2);
   AddTree (TypeNode, TempTree, 1);

   TempTree = Child (RootOfTree(1), 2);
   AddTree (TypeNode, TempTree, 1);

   TempTree = Child (Child (RootOfTree(1), 2), 1);
   AddTree (BooleanTNode, TempTree, 1);
 
   TempTree = Child (Child (RootOfTree(1), 2), 2);
   AddTree (IntegerTNode, TempTree, 1);
}



void ErrorHeader (TreeNode T)
{ 
   printf ("<<< CONSTRAINER ERROR >>> AT ");
   Write_String (stdout,SourceLocation(T));
   printf (" : ");
   printf ("\n");
}


int NKids (TreeNode T)
{
   return (Rank(T));
}



UserType Expression (TreeNode T)
{
   UserType Type1, Type2;
   TreeNode Declaration, Temp1, Temp2;
   int NodeCount;

   if (TraceSpecified)
   {
      fprintf (TraceFile, "<<< CONSTRAINER >>> : Expn Processor Node ");
      Write_String (TraceFile, NodeName(T));
      fprintf (TraceFile, "\n");
   }
     
   switch (NodeName(T))
   {
      case LENode :
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
      
      case GENode :
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

      case AndNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF 'and' MUST BE THE SAME TYPE\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case OrNode :
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
         Type1 = Expression (Child(T,1));

         if (Rank(T) == 2)
            Type2 = Expression (Child(T,2));
         else  
            Type2 = TypeInteger;

         if (Type1 != TypeInteger || Type2 != TypeInteger)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '+' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeInteger);

      case MinusNode : 
         Type1 = Expression (Child(T,1));

         if (Rank(T) == 2)
            Type2 = Expression (Child(T,2));
         else  
            Type2 = TypeInteger;

         if (Type1 != TypeInteger || Type2 != TypeInteger)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '-' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeInteger);

      case NotNode :
         Type1 = Expression (Child(T,1));
         if (Type1 != TypeBoolean)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENT OF 'not' MUST BE TYPE BOOLEAN\n");
            printf ("\n");
         }
         return (TypeBoolean);

      case ModNode : 
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != TypeInteger || Type2 != TypeInteger)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF 'mod' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeInteger);

      case MultNode : 
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != TypeInteger || Type2 != TypeInteger)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '*' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeInteger);

      case DivNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != TypeInteger || Type2 != TypeInteger)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '/' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeInteger);

      case ExpNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != TypeInteger || Type2 != TypeInteger)
         {
            ErrorHeader(Child(T,1));
            printf ("ARGUMENTS OF '**' MUST BE TYPE INTEGER\n");
            printf ("\n");
         }
         return (TypeInteger);

      case ReadNode :
         return (TypeInteger);

      case TrueNode :
         return (TypeBoolean);

      case FalseNode :
         return (TypeBoolean);

      case EofNode :
         return (TypeBoolean);

      case IntegerNode : 
         return (TypeInteger);


      case IdentifierNode :
         Declaration = Lookup (NodeName(Child(T,1)), T);
         if (Declaration != NullDeclaration)
         {
            Decorate (T, Declaration);
            return (Decoration(Declaration));
         }
         else{
            printf("Variables not declared\n");
            return (TypeInteger);
}


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
   TreeNode Type1, Type2, Type3;
   int Temp;

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
         DTEnter(LOOP_CTXT,T,T);
         DTEnter(FOR_CTXT,T,T);
         Name1 = NodeName(Child(Child(T,1),1));
         Name2 = NodeName(Child(Child(T,NKids(T)),1));

         if (Name1 != Name2)
         {
           ErrorHeader(T);
           printf ("PROGRAM NAMES DO NOT MATCH\n");
           printf ("\n");
         }

         for (Kid = 2; Kid <= NKids(T)-1; Kid++)
            ProcessNode (Child(T,Kid));
         CloseScope();
         break;


      case TypesNode :  
         for (Kid = 1; Kid <= NKids(T); Kid++)
            ProcessNode (Child(T,Kid));
         TypeBoolean = Child(T,1);
         TypeInteger = Child(T,2);
         break;


      case TypeNode :
         DTEnter (NodeName(Child(T,1)),T,T);
         break;


      case DclnsNode :
         for (Kid = 1; Kid <= NKids(T); Kid++)
            ProcessNode (Child(T,Kid));
         break;


      case DclnNode :

	 Name1 = NodeName (Child(T, NKids(T)));

         Type1 = Lookup (Name1,T);

         for (Kid  = 1; Kid < NKids(T); Kid++)
         {
            DTEnter (NodeName(Child(Child(T,Kid),1)), Child(T,Kid), T);
            Decorate (Child(T,Kid), Type1);

         }
         break;


      case BlockNode :
         for (Kid = 1; Kid <= NKids(T); Kid++)
            ProcessNode (Child(T,Kid));
         break;


      case AssignNode :
      case SwapNode :
         Type1 = Expression (Child(T,1));
         Type2 = Expression (Child(T,2));

         if (Type1 != Type2)
         {
            ErrorHeader(T);
            printf ("ASSIGNMENT/SWAP TYPES DO NOT MATCH\n");
            printf ("\n");
         }
	 Temp = Lookup(FOR_CTXT);
	 while (NodeName(Temp) != ProgramNode){
	    if (NodeName(FK(FK(Temp)) = NodeName(FK(FK(T)){
		ErrorHeader(T);
                printf ("Cannot assign inside a 'for'\n");
                printf ("\n");
	    }
	    Temp = Decoration(Temp);
	 }
         break;


      case OutputNode :
         for (Kid = 1; Kid <= NKids(T); Kid++)
            if (Expression (Child(T,Kid)) != TypeInteger)
            {
               ErrorHeader(T);
               printf ("OUTPUT EXPRESSION MUST BE TYPE INTEGER\n");
               printf ("\n");
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

      case RepeatNode :
         if (Expression (Child(T,NKids(T))) != TypeBoolean)
         {
            ErrorHeader(T);
            printf ("REPEAT EXPRESSION NOT OF TYPE BOOLEAN\n");
            printf ("\n");
         }
         for (Kid = 1; Kid < NKids(T); Kid++){
            ProcessNode (Child(T,Kid));
         }
         break;

      case LoopNode :
         OpenScope();
         DTEnter(LOOP_CTXT,T,T);

         for (Kid = 1; Kid <= NKids(T); Kid++)
            ProcessNode (Child(T,Kid));
         CloseScope();
         if(Decoration(T)==0){
            ErrorHeader(T);
            printf ("WARNING: No 'exit'\n");
            printf ("\n");
         }
         break;

      case ExitNode :
         Temp = Lookup(LOOP_CTXT,T);
         if (NodeName(Temp) != LoopNode){
            ErrorHeader(T);
            printf ("'exit' on a wrong context\n");
            printf ("\n");}
         Decorate(T,Temp); 
         Decorate(Temp,T);
         break;

      case UptoNode :
      case DowntoNode :
         Temp = Lookup(FOR_CTXT,T);
	 Decorate (T,Temp);
	 OpenScope();
	 DTEnter(FOR_CTXT,T,T);
	 DTEnter(LOOP_CTXT);   //  disallows “exit” not sure
	 for (Kid = 1; Kid <= NKids(T); Kid++){
            ProcessNode (Child(T,Kid));
         }
	 while (NodeName(Temp) != ProgramNode){
            if (NodeName(FK(FK(Temp)) = NodeName(FK(FK(T)){ //QUE ES!!!
               ErrorHeader(T);
               printf ("cannot modify variable from inside the 'for'\n");
               printf ("\n");
            }
            Temp = Decoration(Temp);
         }
	 CloseScope();
         break;

      case NullNode : 
         break;

      default :
         ErrorHeader(T);
         printf ("UNKNOWN NODE NAME ");
         Write_String (stdout,NodeName(T));
         printf ("\n");

   }  /* end switch */
}  /* end ProcessNode */

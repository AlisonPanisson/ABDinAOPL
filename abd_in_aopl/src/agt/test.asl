// Agent sample_agent in project teste

/* Initial beliefs and rules */

/* Rules */
has_argument(Content,Justification):- argument(Content,Justification) & not(.empty(Justification)).
has_argument_against(Content,Comp,Justification):- complement(Content,Comp) & argument(Comp,Justification) & not(.empty(Justification)).

inCS(Content):- .my_name(AgentName) & agents(Agents) & .term2string(AgentsT,Agents) &.member(cs(AgentName,CS),AgentsT) & .sublist(Content,CS).

/* Initial goals */

{ include("reasoning/defeasible_reasoning.asl") }
{ include("performatives.asl") }
 
/* Plans */

+!argument(X) : argument(X,Content) <- .print("The argument: ", Content).


/* Response to new dialogue (ACCEPT or REFUSE) */	
+dialogue(X)[source(self)] <- true.
+dialogue(X)[source(Ag)]: acceptdialogue(X) <- performatives.send(Ag,acceptdialogue,X).  
+dialogue(X)[source(Ag)]: not acceptdialogue(X) <- performatives.send(Ag,refusedialogue,X). 

+!continueDialogue(Dialogue): subject(Subject,DT) & argument(Subject,Arg)
	<-  .my_name(Name);
		lookupArtifact(Dialogue,A)
		focus(A);
		allAgents(Ag)[artifact_id(A)];
		.term2string(AgT,Ag);
		addCS(Arg);
		performatives.send(AgT,assert,Arg).
		
+!responseAssert(Sender,[defeasible_rule(C,S)|T]): .print(C, "  ", S)
	<-	if(has_argument_against(C,Comp,Argument)){
			if(not inCS(Argument)){
				allAgents(Teste);
				addCS(Argument);
				+waiting_discuss(T);  
				performatives.send(Sender,assert,Argument)
			}else{
				!responseAssert(Sender,T);
			}
		}else{
			!responseAssert(Sender,T);
		}.

+!responseAssert(Sender,[X|T]): true
	<-	!responseAssert(Sender,T).

+!responseAssert(Sender,[]): waiting_discuss(T)
	<-	-waiting_discuss(T);
	    .print("Discuss: ", T);
		!responseAssert(Sender,T).
			
+!responseAssert(Sender,[]): not waiting_discuss(T) & passed
	<-	.print("End!").
	
+!responseAssert(Sender,[]): not waiting_discuss(T) & not passed
	<-	.print("End!");
		+passed
		performatives.send(Sender,pass,_).

	
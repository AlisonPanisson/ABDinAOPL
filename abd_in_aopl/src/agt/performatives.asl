// Agent locutions in project performatives

number_of_dialogues(0).
ctj(Content):- true.
acceptdialogue(X):- true.

/* ######################################## Receiving ######################################## */ 

/* ######## OpenDialogue ######### */
@kqmlReceivedOpenDialogue
+!kqml_received(Sender, opendialogue, Content, MsgId)
   <- 	.print("Received opendialogue message with id: ", Content);
   		.add_nested_source(dialogue(Content), Sender, CA);
   		+CA;
   		.print("Added belief: ", CA). 
   		
/* ######## CloseDialogue ######### */   		
@kqmlReceivedCloseDialogue
+!kqml_received(Sender, closedialogue, Content, MsgId)
   <- 	.print("Received closedialogue message with id: ", Content);
   		.add_nested_source(dialogue(Content), Sender, CA);
   		-CA;
   		.print("Deleted belief: ", CA).
   		
/* ######## AcceptDialogue ######### */   	 //FAZER AINDA	
@kqmlReceivedAcceptDialogue
+!kqml_received(Sender, acceptdialogue, Content, MsgId)
   <- 	.print("Received acceptdialogue message with id: ", Content);
   		lookupArtifact(Content,A);
        focus(A);
   		confirmAgent(Sender)[artifact_id(A)].
   		
   		
 +continueDialogue(ID) <- .print("Continuing Dialogue ", ID); !!continueDialogue(ID).
 
 //CONTINUAR APARTIR DO CONTINUE DIALOGUE
   		
  
/* ######## RefuseDialogue ######### */   	 //FAZER AINDA	
@kqmlReceivedRefuseDialogue
+!kqml_received(Sender, refusedialogue, Content, MsgId)
   <- 	lookupArtifact(Content,A);
        focus(A);
        removeAgent(Sender)[artifact_id(A)];
        .print("Received refusedialogue message with id: ", Content).  		
 
/* ######## Assert ######### */  		
@kqmlReceivedAssert
+!kqml_received(Sender, assert, Content, MsgId): .add_nested_source(Content, Sender, CA)
   <- 	.print("Received assert message with ", CA);
   	 	!responseAssert(Sender,CA). // IMPLEMENT A MODULE

/* ######## Accept ######### */
@kqmlReceivedAccept
+!kqml_received(Sender, accept, Content, MsgId): .add_nested_source(Content, Sender, CA)
   <- 	.print("Received accept message with ", CA);
   	 	+CA;
   	 	!receiveAccept(Sender,Content). // IMPLEMENT A MODULE
 
/* ######## Retract ######### */  	 	
@kqmlReceivedRetract
+!kqml_received(Sender, retract, Content, MsgId): .add_nested_source(Content, Sender, CA)
   <- 	.print("Received retract message with ", CA);
   	 	-CA.
   	 	

/* ######## Question ######### */
@kqmlReceivedQuestion
+!kqml_received(Sender, question, Content[dialogue(D)], MsgId): ctj(Content)
   <- 	.print("Received question message with ", Content);
	    ?argument(Content,Justification);
	    // I changed (remove D as receiver)
	    allAgents(Ag)[artifact_id(A)];
		.term2string(AgT,Ag);
	    performatives.send(AgT,justify,Justification).
        	 	
/* ######## Justify ######### */
@kqmlReceivedJustify
+!kqml_received(Sender, justify, Content, MsgId): .list(Content)
   <- 	.print("Received justify message with ", Content);
        !add_all_kqml_received(Sender,Content);
        !responseJustify(Sender,Content). // IMPLEMENT A MODULE
        
@kqmlReceivedJustifyList1
+!add_all_kqml_received(_,[]).   

@kqmlReceivedJustifyList2
+!add_all_kqml_received(Sender,[H|T])
   :  .literal(H) & 
      .ground(H)
   <- .add_nested_source(H, Sender, CA);
      +CA;
      !add_all_kqml_received(Sender,T).

@kqmlReceivedJustifyList3
+!add_all_kqml_received(Sender,[_|T])
   <- !add_all_kqml_received(Sender,T).
   	 	

/* ######## Challenge ######### */
@kqmlReceivedChallenge
+!kqml_received(Sender, challenge, Content[dialogue(D)], MsgId): ctj(Content)
   <- 	.print("Received challenge message with ", Content[dialogue(D)]);
	    ?argument(Content,Justification);
	    // I changed (remove D as receiver)
	    allAgents(Ag)[artifact_id(A)];
		.term2string(AgT,Ag);
	    performatives.send(AgT,justify,Justification);
	    ?comp(Content,CompContent);
	    .add_annot(CompContent, dialogue(D), CompCA);
	    .add_nested_source(CompCA, Sender, CompCA2);
	    !responseChallenge(Sender,CompCA2).	  // IMPLEMENT A MODULE
	    
@kqmlReceivedPass
+!kqml_received(Sender, pass, _, MsgId)
   <- 	!responseAssert(Sender,[]). 
	    
	    
/* ######################################## Sending ######################################## */  
	
/* Send challenge */
+!send(Aid,challenge,Content[dialogue(Did)]): true
	<- 	
		lookupArtifact(Did,A);
	    focus(A);
	    ?comp(Content,ContentN);
	    addCS(ContentN)[artifact_id(A)];
	    allAgents(Agents)[artifact_id(A)];
	    .term2string(Temp,Agents);
//	    .term2string(D,Did);
	    .add_annot(Content, dialogue(Did), ContentCA);
	    .add_annot(ContentN, dialogue(Did), ContentNCA);
	    performatives.send(Aid,challenge,ContentCA);
	    performatives.send(Temp,assert,ContentNCA).


/* Open the dialogue  */ 
+!opendialogue(Agents,Subject): true
	<- 	?number_of_dialogues(X);
		-+number_of_dialogues(X+1);
		?number_of_dialogues(N);
		.concat("d",N,Name);
		makeArtifact(Name,"artifacts.Dialogue",[Agents],D);
	    focus(D);
	    +subject(Subject,Name);
	    .print("Subject:", subject(Subject,NameT));
	    ?id(ID)[artifact_id(D)];
	    allAgents(Ag)[artifact_id(D)];
	    .print("Agents: ", Ag);
	    .term2string(Temp,Ag);
	    performatives.send(Temp,opendialogue,ID);
	    .my_name(AName);
	    confirmAgent(AName)[artifact_id(D)]; 
	    +dialogue(ID).
	    
/* Close the dialogue  */ 
+!closedialogue(D1): true  //Did is the dialogue identifier
	<-  lookupArtifact(D1,D);
		focus(D);
		closedialogue[artifact_id(D)]; //close the dialogue
		 allAgents(Ag)[artifact_id(D)];
	    .term2string(Temp,Ag);
	    performatives.send(Temp,closedialogue,D1);
	    -dialogue(D1).

+!create_artifact_Dialogue(Name,D,T)
	<- 	makeArtifact(Name,"artifacts.Dialogue",[T],D).
   	 		


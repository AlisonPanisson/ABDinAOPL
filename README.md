# ABDinAOPL -- An Interface for Argumentation-Based Dialogues in Agent-Oriented Programming Languages


This interface was implemented using JaCaMo Framework. More information about JaCaMo is available [here](http://jacamo.sourceforge.net/).
Also, you need to be familiar with [Jason](http://jason.sourceforge.net/wp/) agent-oriented programming language.

## Installing JaCaMo Eclipse Plugin
- [Install Eclipse IDE](https://www.eclipse.org/downloads/)
- Install JaCaMo plugin following the instruction in this [link](http://jacamo.sourceforge.net/eclipseplugin/tutorial/)
- Create a new JaCaMo Project 

## Importing the Argumentation-Based Dialogue Mechanism

- Download the argumentation-based dialogue mechanism fromthis project
- Upload those files to your JaCaMo Project
- Include the performatives as part of your agents' code using the following command:

```javascript
{ include("performatives.asl") }
```
- Include the dialogue artifacts to your project and make sure to use the following archiecture in your agents: 

```javascript
ag-arch: infra.dist.DistAgentArch 
```
- Also, use the upadated internal action  ```.send ``` available in ../src/env/performatives/send.java when communicating. 


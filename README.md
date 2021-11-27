# coq_set_theory_and_definitions
an implementation of the definite description operator for first order set theory.

Compilation instructions: put in a folder and enter "make" in a terminal from here.

Library usage: 

In a .v file: include the line "Require Import Set_and_Definitions." at the beginning of your file.

With coqtop (in a linux terminal):
From the folder where the library has been build, launch coqtop with the command "coqtop -Q . Setdef -l Sets_and_Definitions.v".
Alternatively, you may launch coqtop first, then from here enter the commands:<<

Add LoadPath "./" as SetDef.
Require Import Setdef.Sets_and_Definitions.

>>

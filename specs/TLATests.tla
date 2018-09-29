------------------------------ MODULE TLATests ------------------------------

EXTENDS Integers
VARIABLES bar

Init == bar = -1

Next == bar' = CHOOSE v \in 2..99 : TRUE

\* how do we make the TLC check that this is broken by the CHOOSE
\* expression?
TypeOK == bar < 5
\* answer: there's no non-determinism in math and in TLA+
\* TLC will always get the same number when it evaluates the CHOOSE expression

=============================================================================
\* Modification History
\* Last modified Sat Sep 29 19:45:46 CEST 2018 by DavidRueda
\* Created Sat Sep 29 19:13:03 CEST 2018 by DavidRueda

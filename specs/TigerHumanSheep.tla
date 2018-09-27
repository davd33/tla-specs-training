-------------------------- MODULE TigerHumanSheep --------------------------

(***************************************************************************)
(* This module specifies what a man, accompanied by a sheep, some food and *)
(* a tiger, can do in order to cross a river with a boat and according to  *)
(* the following rules:                                                    *)
(*                                                                         *)
(*  - The boat can only fit for the man and one of the other               *)
(*    elements (food, sheep, tiger).                                       *)
(*  - If the sheep is left alone on one side of the river with             *)
(*    the food, the sheep will eat the man's food.                         *)
(*  - If the tiger is left alone with the sheep, the tiger                 *)
(*    will eat the sheep.                                                  *)
(*  - The puzzle is completed once the man, the sheep, the tiger           *)
(*    and the food have crossed the river.                                 *)
(*  - The tiger does not eat the food the man caries since                 *)
(*    it's only vegs.                                                      *)
(***************************************************************************)

EXTENDS Integers

(***************************************************************************)
(* Variable bRSide represents the side of the river on which an animal of  *)
(* the BEINGS set stands on (the initial side is 0 and the other side is   *)
(* 1).                                                                     *)
(***************************************************************************)
VARIABLES bRSide
CONSTANTS SHEEP, FOOD, TIGER, MAN, BEINGS

haveNotCrossed(being1, being2) ==
  /\ bRSide[being1] = 0
  /\ bRSide[being2] = 0
haveCrossed(being1, being2) ==
  /\ bRSide[being1] = 1
  /\ bRSide[being2] = 1

changeBeingsSide(being1, being2) ==
  /\ bRSide[being1] = bRSide[being2]
  /\ bRSide' = [bRSide EXCEPT ![being1] = 1 - bRSide[being1],
                              ![being2] = 1 - bRSide[being2]]

(***************************************************************************)
(* For each the four elements of the enigma:                               *)
(*  - 0 means that it has not yet crossed or has come back to the original *)
(*    border of the river.                                                 *)
(*  - 1 means that it has crossed the river and is now on the other side.  *)
(***************************************************************************)
TypeOK == bRSide \in [BEINGS -> 0..1]

(***************************************************************************)
(* First, all beings are on the same river side!                           *)
(***************************************************************************)
Init == bRSide = [b \in BEINGS |-> 0]

(***************************************************************************)
(* Some invariants:                                                        *)
(*  - The sheep cannot be left with the food without man's presence.       *)
(*  - The tiger cannot be left with the sheep without man's presence.      *)
(***************************************************************************)
SheepNotWithFood ==
  IF bRSide[SHEEP] # bRSide[MAN] THEN bRSide[SHEEP] # bRSide[FOOD] ELSE TRUE
TigerNotWithSheep ==
  IF bRSide[TIGER] # bRSide[MAN] THEN bRSide[TIGER] # bRSide[SHEEP] ELSE TRUE
BeingsInvariants == 
  \/ Init
  \/ /\ SheepNotWithFood /\ TigerNotWithSheep

(***************************************************************************)
(* Man takes sheep over.  Behind him, eventually, tiger and food could be  *)
(* left alone.                                                             *)
(***************************************************************************)
TakeSheepOver ==
  /\ haveNotCrossed(MAN, SHEEP)
  /\ changeBeingsSide(MAN, SHEEP)

(***************************************************************************)
(* Man takes tiger over and takes care not to leave sheep and food alone!  *)
(***************************************************************************)
TakeTigerOver ==
  /\ ~ ( bRSide[SHEEP] = bRSide[TIGER] /\ bRSide[FOOD] = bRSide[SHEEP] )
  /\ haveNotCrossed(MAN, TIGER)
  /\ changeBeingsSide(MAN, TIGER)

(***************************************************************************)
(* Man takes the food over and takes care not to leave sheep with tiger.   *)
(***************************************************************************)
TakeFoodOver ==
  /\ ~ ( bRSide[TIGER] = bRSide[FOOD] /\ bRSide[SHEEP] = bRSide[TIGER] )
  /\ haveNotCrossed(MAN, FOOD)
  /\ changeBeingsSide(MAN, FOOD)

(***************************************************************************)
(* Man takes the sheep back, but tiger could stay with food.               *)
(***************************************************************************)
TakeSheepBack ==
  /\ haveCrossed(MAN, SHEEP)
  /\ changeBeingsSide(MAN, SHEEP)

(***************************************************************************)
(* Man takes the tiger back and takes care not to leave the food with the  *)
(* sheep alone!                                                            *)
(***************************************************************************)
TakeTigerBack ==
  /\ ~ ( bRSide[SHEEP] = bRSide[TIGER] /\ bRSide[FOOD] = bRSide[SHEEP] )
  /\ haveCrossed(MAN, TIGER)
  /\ changeBeingsSide(MAN, TIGER)

(***************************************************************************)
(* When the man takes the food back, he shall not let the tiger with the   *)
(* sheep behind him!                                                       *)
(***************************************************************************)
TakeFoodBack ==
  /\ ~ ( bRSide[TIGER] = bRSide[FOOD] /\ bRSide[SHEEP] = bRSide[TIGER] )
  /\ haveCrossed(MAN, FOOD)
  /\ changeBeingsSide(MAN, FOOD)

(***************************************************************************)
(* When the man travels alone, he shall not let the tiger with the sheep   *)
(* or the sheep with the food behind him!                                  *)
(***************************************************************************)
ManTravelsAlone ==
  /\ ~ ( bRSide[MAN] = bRSide[SHEEP] /\ bRSide[SHEEP] = bRSide[FOOD] )
  /\ ~ ( bRSide[MAN] = bRSide[TIGER] /\ bRSide[TIGER] = bRSide[SHEEP] )
  /\ bRSide' = [bRSide EXCEPT ![MAN] = 1 - bRSide[MAN]]

NotAllCrossed == \E b \in BEINGS : bRSide[b] # 1
AllCrossed == \A b \in BEINGS : bRSide[b] = 1

Next == 
  \/ TakeSheepOver
  \/ TakeSheepBack
  \/ TakeTigerOver
  \/ TakeTigerBack
  \/ TakeFoodOver
  \/ TakeFoodBack
  \/ ManTravelsAlone

=============================================================================
\* Modification History
\* Last modified Wed Sep 26 17:29:13 CEST 2018 by DavidRueda
\* Created Wed Sep 19 20:07:31 CEST 2018 by DavidRueda

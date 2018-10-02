Training for TLA+
===

This repo is for me to learn TLA+ by specifying logical problems or practical implementations of actual coding.

Notes do read:
 -  [TLA+ Notes](./notes/Notes-1.md)
 -  [Clock paper from Leslie Lamport](./notes/Notes-2.md)



## The man crossing a river

This is a well known riddle. A man, travelling with a tiger, a sheep and food (vegetables), encounter a river that they shall cross.

The man is given a boat that can take him and one of his animal or the food. How will the man make his animal cross the river without loosing any of them or the food.

If the sheep is let alone with the food, the sheep will eat that food. Likewise, if the tiger and the sheep are let alone on one shore, the tiger will eat the sheep.

### The Model

#### CONSTANTS

```
BEINGS <- {"SHEEP","FOOD","TIGER","MAN"}
MAN <- "MAN"
SHEEP <- "SHEEP"
TIGER <- "TIGER"
FOOD <- "FOOD"
```





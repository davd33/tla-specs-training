TLA+ Notes
======



Finding fault-tolerant distributed algorithms is hard.
They're easy to get wrong, and hard to find errors by testing.

We should get the algorithm right before we code.

> Writing and checking a TLA+ spec is the best way I know to do that. _Leslie Lamport_



## Tips

### Primed variables

Only use an expression with a primed variable (`v' = ...` or `v' \in ...`) when `...` is an expression that does not contain any primed variable.

### Every value is a Set!

Even values like `42` and `"abc"` are sets, but the semantics of TLA+ don't say what the elements of the sets are, hence TLC can't evaluate an expression like `42 \in "abc"`.



## Vocabulary

| Programming             | Math     |
| ----------------------- | -------- |
| array                   | function |
| index set               | domain   |
| `f[e]` _(used in TLA+)_ | `f(e)`   |

Many popular programming languages allow only index from `0..n`.
**Math and TLA+ allow function to have any set as its domain!** _(Even infinite sets as the set of all integers)_

The first conjunctions of an action formula (e.g. `TMRcvPrepared(r)` in `TwoPhase`) that have no primes are **conditions on the first state of a step**: they are called **enabling conditions**.

**ENABLING CONDITIONS GO FIRST IN AN ACTION FORMULA!**

**An action formula is a formula that contains primed variables.**



## Functions

```
[RM -> ... ]
```

**Set of functions `f` with `f[x] = e` for `x \in S`.**

Example: `rmState \in [RM → {“working”, “prepared”, “committed”, “aborted”}]` means that `rmState` is in the set of all functions indexed by elements of `RM` with values `rmState[rm]` given by the set `{"working", "prepared", "committed", "aborted"}`.



## Records

```
r == [prof |-> "Fred", num |-> 42]
```

The above definition defines `r` to be a **record of two fields `prof` and `num`**.
The values of the fields are: `r.prof = "Fred"` and `r.num = 42`. 
Changing the order of the fields make no difference! 



```tla+
[prof: {"Fred","Ted","Ned"}, num: 0..99]
```

The formula above is the set of all records of the form `[prof |-> ..., num |-> ...]`, with the values of its `prof` field in `{"Fred","Ted","Ned"}`,  and the values of its `num` field in `0..99`.

So, the record `[prof |-> "Ted", num: 23]` is in the set above.

`[prof |-> "Ted", num: 23]` is actually a function `f` with domain `{"prof", "num"}` such that `f["prof"] = "Ted"` and `f["num"] = 23`.

`f.prof` is an abbreviation for `f["prof"]`.

```
[f EXCEPT !["prof"] = "Red"]
\* can be abbreviated as:
[f EXCEPT !.prof = "Red"]
```



## Triples

```<<rmState, tmState, msgs>>``` is an **ordered** triple.




## Sets

***A set cannot contain several copies of the same element.***

The **subset of** a set is written in TLA+ as follows: **`\subseteq`**.

The **union of** two sets is written: **`\cup` or `\union`**.

**Adding an element to a set** can be done with a union: `tmPrepared' = tmPrepared \union {r}`.

#### Symmetry sets

In `TwoPhase` spec, all RMs are identical / interchangeable.

Suppose that `RM = {r1, r2, r3}`, replacing `r1` with `r3` in one possible state yields another possible state. Exchanging `r1` and `r3` in all states of a behaviour `b` allowed by `TwoPhase` produces a behaviour `b1-3` allowed by `TwoPhase`. **Therefore, TLC does not have to check whether some properties of `TwoPhase` holds for behaviour `b1-3` if it has checked that it holds for behaviour `b`.**

**Because the latter observation holds for interchanging any two elements of RM, RM is a symmetry set of the specification `TwoPhase`.**

TLC will check fewer states if the model sets a symmetry set to a set of model values.
TLC may miss errors if you claim a set is symmetrical when it's not!



## Other formulas

### INSTANCE

Imports the definitions from another specification (e.g. `TCommit`) into the current module (e.g. `TwoPhase`).

### CHOOSE

```
CHOOSE v \in S : P
```

The formula above equals some such `v` if there is  a `v` in `S` for which `P` is true. If there's more than one, then the semantics of TLA+ don't specify which one. Else, if there's no such `v` then the value of the `CHOOSE` expression is completely unspecified (TLC will report an error if that's the case when it tries to evaluate the expression).

For instance the value `v` of the following expression `CHOOSE i \in 0..99 : TRUE` is an unspecified integer between 1 and 99.

**A `CHOOSE` expression always equals itself! There is no non-determinism in a mathematical expression.** TLC will always get the same value when evaluating a `CHOOSE` expression: we should not care what value.

`x' \in 0..99` allows the value of `x` in the next state to be any number in `1..99`.

`x' = CHOOSE i \in 0..99 : TRUE` allows the value of `x` in the next state to be one particular number.

### UNCHANGED

`UNCHANGED << foo, bar >>` is equivalent to:

```
foo' = foo
bar' = bar
```








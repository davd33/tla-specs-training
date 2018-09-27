TLA+ Notes
======



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


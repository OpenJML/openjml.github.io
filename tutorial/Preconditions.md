---
title: JML Tutorial - Preconditions (requires clauses)
---

Sometimes a method may only be called in certain combinations of program state and actual
arguments. Such restrictions are called *preconditions* and
are written with a *requires* clause.

For example, a method to compute an integer square root requires its
input to be non-negative:
```
%include T_requires1.java
```

Other common preconditions are that a parameter is not null (e.g., `o != null`)
or that an index is in range for an array (`0 <= i < a.length`).

A method's specifications may include more than one requires clause. For example,
```
%include T_requires2.java
```

There may be an order to the requires clauses. In this case, the `a.length` in
the second clause is undefined if `a` is null. Thus we also need the
condition stated in the first clause, and it must be stated before the
second clause. Reversing the order will result in an error:
```
%include T_requires3.java
```
produces
```
%include T_requires3.out
```

Ensures clauses may be mixed in order with the requires clauses, but good,
and clearer, style suggests putting all requires clauses first and then
all ensures clauses.

LAST_MODIFIED

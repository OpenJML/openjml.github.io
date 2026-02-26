---
title: JML Tutorial - Minimizing replicated specifications (initially, constraint, invariant clauses)
---

Sometimes certain properties must hold at the end of every constructor or every method.
Then the specifications for each method or constructor would have to repeat the same specification clause in every constructor or method's specification.
However, there is a danger that: (a) such a clause will be forgotten for some constructor or method and (b) if the clause needs to be modified, it will not be correctly changed in every place it appears.

So JML has a few features to coalesce such replicated clauses. These clauses are part of the _class_ declaration, but apply to every method or constructor in the class (or interface) as described below.

## Initially clauses

An `initially` clause at the class level is equivalent to a corresponding `ensures` clause at the end of every constructor, including any unwritten default constructor. For example, suppose we are constructing rectangles and want to ensure that, at least upon construction, every such rectangle has a length larger than its width, which is larger than 0.  We might write
```
{% include_relative T_initially1.java %}
```
This yields
```
{% include_relative T_initially1.out %}
```
This verification failure is understandable. We did not specify a precondition that `0 < width < length`, so the stated initially clause cannot be fulfilled.
But why is there no failure for the second constructor? The second constructor calls `this(0,0)`, using the first constructor. Because it is calling that
constructor, it only uses that constructor's specifications in reasoning about its own implementation. So the call of the first constructor by the second constructor sees
```
   assume \let width = 0 && length = 0 in (this.width == width && this.length == length) 
   assume 0 < this.width < this.length
   assert 0 < this.width < this.length
```
That is, it assumes the first constructor's postcondition and assumes the first constructor satisfies the initially clause and then seeks to prove that the initially clause is satisfied after the body of the second constructor. This would be a trivial proof, but actually is a vacuous proof because the middle statement in the display above is assuming false. And that results in no verification complaint being issued about the second constructor.

If we insert a precondition to fix the verification of the first constructor, we now have
```
{% include_relative T_initially2.java %}
```
which yields:
```
{% include_relative T_initially2.out %}
```
Now the first constructor passes verification, but the second one does not. The reason is obvious: 
the size we have given for a default rectangle (0 by 0) does not satisfy our desired `initially` postcondition, which was enforced by the new precondition on the first constructor.
To fix this failure, we would have a to pick different sizes -- 1x2 perhaps.

## Constraint clauses

Constraint clauses are postcondition clauses that apply to every non-constructor method. A non-static constraint clause applies only to non-static
methods. The typical use of a constraint clause is to state some relationship between the pre-state and post-state of the method. 
For example, a class may have a `count` field that counts how many times some method of the class has been called.
Because it is a postcondition, a constraint clause may use the `\old` construct to refer to the pre-state of the method.

We could then write the following:
```
{% include_relative T_constraint.java %}
```
which produces the following result
```
{% include_relative T_constraint.out %}
```
Here `m1` increments `count`, so it satisfies the constraint. `m2` does not increment `count`, so it causes a verification error for the constraint. `m3` is OK, even though it does not
increment `count` because the non-static constraint does not apply to the static method `m3`.


## Invariants

Invariants also are predicates that apply to every method, but they are more extensive and complex than constraints. An invariant is typically used to
express a property that must be true for a data structure to be valid or self-consistent. For example, a class may have a `count` that must always be non-negative, or two arrays that must be the same length, or an array that must be sorted. Invariants are used to express properties like these.

Since these are validity properties, 
* a method may assume that the invariants are true in its pre-state
* and must ensure that the invariants are still true (or true again) in its post-state

Further detail on invariants is given in a [dedicated lesson on the topic](Invariants).


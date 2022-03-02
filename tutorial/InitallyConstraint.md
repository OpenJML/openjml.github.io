---
title: JML Tutorial - Minimizing replicated specifications: initially, constraint, invariant clauses
---

Sometimes it is the case that certain properties must hold at the end of every constructor or every method.
Then the specifications for each method or constructor have to repeat the same specification clause.
There is a dnager that (a) such a clause will be forgotten for some constructor or method and (b) if the clause needs to be modified, it will not be correctly changed in every place it appears.

So JML has a few features to coalesce such replicated clauses. These clauses are part of the _class_ declaration, but apply to every method or constructor as described below.

## Initially clauses

An `initially` clause at the class level is equivalent to a corresponding `ensures` clause at the end of every constructor, including an unwritten default constructor. For example, suppose we are constructing rectangles and want to ensure that, at least upon construction, every such rectangle has a length larger than its width, which is larger than 0.  We might write
```
T_initially1.java
```
This yields
```
T_initially1.out
```
This verification failure is understandable. We did not specify a precondition that `0 < width < length`, so the stated initially clause cannot be fulfilled.
But why is there no failure for the second constructor? The second constructor calls `this(0,0)`, using the first constructor. Because it is calling that
constructor, it only uses that constructor's specifications in reasoning about its own implementation. So the second constructor sees
```
   assume \let width = 0 && length = 0 in (this.width == width && this.length == length) 
   assume 0 < this.width < this.length
   assert 0 < this.width < this.length
```
That is, it assumes the first constructor's postcondition and assumes the first constructor satisfies the initially clause and then seeks to prove that the initially clause is satisfied. This would be a trivial proof, but actually is a vacuous proof because the middle statement in the dispaly above is assuming false. And that results in no verification complaint being issued about the second constructor.

If we insert a precondition to fix the verification of the first constructor, we now have
```
// openjml --esc T_initially2.java
public class T_initially2 {

  public int width;
  public int length;

  //@ requires 0 < width < length;
  //@ ensures this.width == width && this.length == length;
  public T_initially2(int width, int length) {
    this.width = width;
    this.length = length;
  }

  //@ ensures this.width == 0 && this.length == 0;
  public T_initially2() {
    this(0,0);
  }

  //@ public initially 0 < width < length;

}
```
which yeilds
```
T_initially2.java:16: verify: The prover cannot establish an assertion (Precondition: T_initially2.java:9:) in method T_initially2
    this(0,0);
        ^
T_initially2.java:9: verify: Associated declaration: T_initially2.java:16:
  public T_initially2(int width, int length) {
         ^
T_initially2.java:7: verify: Precondition conjunct is false: 0 < width < length
  //@ requires 0 < width < length;
                         ^
3 verification failures
```
Now the first constructor passes verification, but the second one does not. The reason is obvious: the size we have given for a default rectangle (0 by 0) doe s not satisfy our desired initially postcondition. We'll have a to pick a different size -- 1x2 perhaps.

## Constraint clauses

TODO


## Invariants

TODO - just a brief introduction to invariants here. More discussion on a page of its own.



_Last modified: 2022-03-02 17:41:36_
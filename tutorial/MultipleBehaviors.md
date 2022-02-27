---
title: Multiple Method Behaviors
---

## Multiple behaviors

So far our method specifications have been simple sequences of clauses: pre-, frame- and post-conditions.
But as methods become more complex it is helpful to separate the method specification into multiple 
 _specification cases_, which can be thought of as different _behaviors_.

Each behavior is a simple sequence of clauses, with its own preconditions, postconditions, etc.
The specification can consist of multiple behaviors, connected by the keyword `also`.
For example,
```
// openjml --esc T_MultipleBehaviors1.java
public class T_MultipleBehaviors1 {
  //@  requires c >= a && c >= b;
  //@  ensures \result == c;
  //@ also
  //@  requires b >= a && b >= c;
  //@  ensures \result == b;
  //@ also
  //@  requires a >= b && a >= c;
  //@  ensures \result == a;
  //@ pure
  public int max(int a, int b, int c) {
    return a >= b ? ( c >=  a ? c : a) : (c >= b ? c : b);
  }
}
```
The specification here is a bit more verbose than the code, but it separates out the cases a bit more readably than the code does.
Furthermore, by writing the goal of the method in two different ways, an exchange of 'a' for 'b' or '<' for '>' is readily caught by OpenJML.

There are a few points to note:
* There is no order to the behaviors; they can be written in any order that is understandable.
* Every behavior applies on its own and must hold by itself --- there is no if-then-else  among them. If a behavior's preconditions hold,
then its postconditios must hold, independent of what any other behavior says.

In our example, if `a`, `b`, and `c` are all equal, then the precondiition (`requires` clause) of each of the three behaviors is true.
So the postconditions of each of the behaviors must also be true.  Fortunately they all agree.

As an experiment, this example introduces a mistake in one behavior:
```
// openjml --esc T_MultipleBehaviors2.java
public class T_MultipleBehaviors2 {
  //@  requires c >= a && c >= a;
  //@  ensures \result == c;
  //@ also
  //@  requires b >= a && b >= c;
  //@  ensures \result == b;
  //@ also
  //@  requires a >= b && a >= c;
  //@  ensures \result == a;
  //@ pure
  public int max(int a, int b, int c) {
    return a >= b ? ( c >=  a ? c : a) : (c >= b ? c : b);
  }
}
```
which yields this result
```
T_MultipleBehaviors2.java:13: verify: The prover cannot establish an assertion (Postcondition: T_MultipleBehaviors2.java:4:) in method max
    return a >= b ? ( c >=  a ? c : a) : (c >= b ? c : b);
    ^
T_MultipleBehaviors2.java:4: verify: Associated declaration: T_MultipleBehaviors2.java:13:
  //@  ensures \result == c;
       ^
2 verification failures
```
The verification failure message points to the postcondition on line 4, which narrows our debugging to the relationship between
that behavior and the code. A little inspection shows a typo at the end of the precondition on line 3.

## Separating normal from exceptional behaviors

A very common use of multiple behaviors is to separate normal execution from exceptions. For example,
```
// openjml --esc T_MultipleBehaviors3.java
public class T_MultipleBehaviors3 {

    //@  requires a != null;
    //@  requires 0 <= i <= j <= a.length;
    //@  ensures true;
    //@  signals (Exception e) false;
    //@ also
    //@  requires a == null || !(0 <= i <= j <= a.length);
    //@  signals_only IllegalArgumentException;
    //@  ensures false;
    public void inrange(int[] a, int i, int j) { 
        if (a == null) throw new IllegalArgumentException();
        if (i < 0 || j < i || a.length < j) throw new IllegalArgumentException();
        return;
    }
}
```
The code in this example does some parameter validation checks. If the checks fail an exception is thrown.
The method could go on to do something useful, but for this example, it just returns.
There are then two behaviors. 
* In the normal case the arguments satisfy the checks and the method just returns normally;
that is the first behavior --- the ensures postcondition is `true` (which could be omitted entirely), which just states that
the method is allowed (but not required) to return normally; the signals postcondition is flase, which states that the under
these preconditions, the method is _not_ allowed to throw an exception.
* The second behavior is the exceptional case. Here one or the other of the argument validation checks fails. In this case, the postcondition is `ensures false`, whcih means that the method is _not_ allowed to return normally; the default. omitted `signals true` clause says that an exception is allowed; the `signals_only` clause says that if there is an exception it must be an `IllegalArgumentException` (the only one listed).

We could even separate out two kinds of exceptions:
```
// openjml --esc T_MultipleBehaviors4.java
public class T_MultipleBehaviors4 {

    //@  requires a != null;
    //@  requires 0 <= i <= j <= a.length;
    //@  ensures true;
    //@  signals (Exception e) false;
    //@ also
    //@  requires a == null || !(0 <= i <= j <= a.length);
    //@  signals_only NullPointerException, ArrayIndexOutOfBoundsException;
    //@  ensures false;
    public void inrange(int[] a, int i, int j) { 
        if (a == null) throw new NullPointerException();
        if (i < 0 || j < i || a.length < j) throw new ArrayIndexOutOfBoundsException();
        return;
    }
}
```
Now the `signals_only` clause allows the kinds of exceptions, although the specification does not say when each one is thrown. We could go to one more level of specification detail to stipulate that the each exception is thrown just when the appropriate argument validation check fails. Try it as an exercise. There is a question though: what if both checks fail? Should the specification state which exception is thrown in preference to the other? If it does it is constraining the implementation, perhaps overly so.

## Specialized behaviors

The normal and exceptional behaviors illustrated in the previous section are very common, so much so that they have specialized syntax: `normal_behavior` and `exceptional_behavior`. We can rewrite the previous example as 
```
// openjml --esc T_MultipleBehaviors5.java
public class T_MultipleBehaviors5 {

    //@ public normal_behavior
    //@  requires a != null;
    //@  requires 0 <= i <= j <= a.length;
    //@ also public exceptional_behavior
    //@  requires a == null || !(0 <= i <= j <= a.length);
    //@  signals_only NullPointerException, ArrayIndexOutOfBoundsException;
    public void inrange(int[] a, int i, int j) { 
        if (a == null) throw new NullPointerException();
        if (i < 0 || j < i || a.length < j) throw new ArrayIndexOutOfBoundsException();
        return;
    }
}
```
The `normal_behavior` heading implies that no exception is allowed (`signals false`); the `exceptional_behavior` heading says that normal terminatino is not allowed.
A behavior that is neither of these is a simple `behavior`, which is the default when there is no heading.

One other point: any one of the behavior keywords needs a visibility keyword; almost always, as in the example above, the visibility is the same as the method. The absence of a visibility modifier means `package` visibility, just as the absence of a visibility modifier on the method declaration.



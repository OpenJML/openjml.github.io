# Assume statements (`assume` clauses)

Like an `assert` stastement, a JML  `assume` statement may be used in the
body of a method. The effect of an `assume` statement is to instruct
the verification engine to assume, *without proof*, that the given 
predicate is true. Such statements can be used to introduce
facts that are too difficult for the proof engine to prove.
They can also be used to temporarily summarize the effect of preceding code 
for the purpose of attempting to prove later code; then one goes back later
to work with the preceding code until the assumption is successfully 
proven and the `assume` statement can be removed.

For example, consider the following code:
```
// openjml -esc T_assume1.java
public class T_assume1 {
  //@ ensures a[\result] == 0;
  public int findZeroElement(int[] a) {
    int i = 0;
    for (; i < a.length; i++) {
      //@ assume 0 <= i < a.length;
      if (a[i] == 0) break;
    }
    //@ assume 0 <= i < a.length && a[i] == 0;
    return i;
  }
}
```

Here we have stated a postcondition we want in the ensures clause and a sketch
of an implementation to compute it. But we don't know yet how to 
specify the behavior of loops (that is coming later!), so we add some 
assumptions that we expect to be true. With those assumptions, the
above example verifies.

Assume statements can be very helpful in developing a proof of an implementation, but they have a danger. If the given predicate is not actually 
true, then it will be possible to prove invalid statements about a program.
You can even see that in the example above: if the array `a` does not
contain any element that is zero, then the second `assume` statement is
invalid and the postcondition cannot actually be proved.

The situation can even be worse. Consider the following drastic, if trivial, case.
```
// openjml -esc T_assume2.java
public class T_assume2 {
  //@ requires i > 0;
  public void example(int i) {
    //@ assert false; // Blatant verification failure
  }
}
```
Here we have an `assert` statement that is explicitly false. So the verifier
will always report that the assertion is not provable and will produce 
this output:
```
T_assume2.java:5: verify: The prover cannot establish an assertion (Assert) in method example
    //@ assert false; // Blatant verification failure
        ^
1 verification failure
```

But now we add an erroneous `assume` statement, one that contradicts the
precondition. Remember that the precondition is assumed at the start of a 
method implementation and that the `assume` statement
is also silently assumed at its location in the body.
```
// openjml --esc --check-feasibility=none T_assume3.java
public class T_assume3 {
  //@ requires i > 0;
  public void example(int i) {
    //@ assume i < 0;
    //@ assert false; // No error because the precondition and assume statement contradict!
  }
}
```
Now OpenJML issues no verification errors. The effect is just like 
the situation in logic where once a contradiction is assumed, anything,
even false statements, can be proven.

Thus, to emphasize the point: `assume` statements can be very helpful in the course of developing 
a specification and proof of a method implementation, but they should be 
replaced with `assert` statements or removed altogether before a verification
is considered sound.


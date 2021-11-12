# Postconditions (`ensures` clauses)

A method's specification states what the method does,
and not how it is done. The effect of a method is
stated in its _postcondition_, which is written in an 
_ensures_ clause.

Consider this example of a method that computes the maximum of four int values.

```
// openjml -esc T_ensures1.java
public class T_ensures1 {
  //@ ensures \result == a | \result == b | \result == c | \result == d;
  //@ ensures \result >= a & \result >= b & \result >= c & \result >= d;
  public int max(int a, int b, int c, int d) {
    if (a > b) {
        if (c > d) {
            if (a > c) return a;
            else       return c;
        } else {
            if (a > d) return a;
            else       return d;
        }
    } else {
        if (c > d) {
            if (b > c) return b;
            else       return c;
        } else {
            if (b > d) return b;
            else       return d;
        }
    }
  }
}
```


The *ensures* clauses just prior to the method declaration state two 
properties that are expected to hold about the result, which is designated
by the keyword `\result`.

* The result must be equal to one of the four inputs.
* The result must be greater than or equal to each of the four inputs.

The body of the function computes this result. Note that the specification
states the properties of the result but does not state how it is computed.
In fact, the same specification could be used with a different implementation:
```
// openjml -esc T_ensures1a.java
public class T_ensures1a {
  //@ ensures \result == a | \result == b | \result == c | \result == d;
  //@ ensures \result >= a & \result >= b & \result >= c & \result >= d;
  public int max(int a, int b, int c, int d) {
    if (a >= b && a >= c && a >= d) return a;
    if (b >= a && b >= c && b >= d) return b;
    if (c >= a && c >= b && c >= d) return c;
    return d;
  }
}
```

Now how can we check that the implementation actually implements the specification? That is the (or one) purpose of the OpenJML tool.
If we execute (cf. [Execution](Execution))
`openjml -esc tutorial/T_ensures1.java`
we find that the openjml tool completes with no error messages and a success
error code, indicating that the implementation is verified with respect to
the given specification.

Similarly, `openjml -esc tutorial/T_ensures1a.java` indicates that this
second example also verifies.

Now consider a third example:

```
// openjml -esc T_ensures2.java
public class T_ensures2 {
  //@ ensures \result == a | \result == b | \result == c | \result == d;
  //@ ensures \result >= a & \result >= b & \result >= c & \result >= d;
  public int max(int a, int b, int c, int d) {
    if (a > b) {
        if (c > d) {
            if (a > c) return a;
            else       return c;
        } else {
            if (a > d) return a;
            else       return d;
        }
    } else {
        if (c > d) {
            if (b > c) return b;
            else       return c;
        } else {
            if (b > c) return b;
            else       return d;
        }
    }
  }
}
```


Running `openjml -esc tutorial/T_ensures2.java` produces this output (and a non-zero exit code):
```
T_ensures2.java:19: verify: The prover cannot establish an assertion (Postcondition: T_ensures2.java:4:) in method max
            if (b > c) return b;
                       ^
T_ensures2.java:4: verify: Associated declaration: T_ensures2.java:19:
  //@ ensures \result >= a & \result >= b & \result >= c & \result >= d;
      ^
2 verification failures
```

The error message tells us that the specification and implementation are
not consistent; in particular, the `ensures` clause on line 3 is not satisfied
when the method exits on line 18. Some code inspection reveals that there
is an error in the `if` condition on line 9: it should be `b > d` (as it is in example `T_ensures1.java` above).
This is the kind of cut&paste error that can be easy to miss during code inspection.

OpenJML is able to provide more debugging information than just the error
message. Tutorial examples are given under the [Debugging](Debugging) topic.

While in this case the error was in the implementation, the error might 
instead be in the specification. In fact, it is possible that the 
specification and implementation agree, but that they differ from what the user intended.

Another situation can be that the specification is not very specific.
For example, the postcondition could simply be `ensures true;`, which is the
default if no `ensures` clause is given. In this case the implementation
trivially satisfies the specification, _no matter what result the implementation returns_.
However, while no problem arises in verifying the method, it would not be
possible to verify _uses_ of the method in some calling method (unless it
indeed did not matter what result was returned). We will return to this 
subject in [Calling Specified Methods](CallingSpecifiedMethods).

Sometimes you may wish to refer to the value returned by a method in the postcon
dition. This value is referenced as `\result`. Like all JML keywords in expressi
on, `\result` begins with a backslash so it does conflioct with a Java identifie
r. `\result` may only be used in `emnsures` clauses of method specifications for
 methods that return values (and not for constructors). Here is a simple example
:
```
// openjml -esc T_ensures3.java
public class T_ensures3 {
  //@ requires a.length > 0;
  //@ ensures \result == a[0];
  public int fist(int[] a) {
    return a[0];
  }
}
```

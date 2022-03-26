---
title: JML Tutorial - Assert statements (`assert` clauses)
---
A JML *assert* statement states a condition that is expected to hold at a point
within the body of a method. Such statements are not part of a method's interface 
specification, but they can help (either staticly with ESC or at runtime with RAC)  debug the execution of a method
or, sometimes, provide a lemma that aids in the verification of the method body.

An assert statement is simple: in a JML comment, it is just the **assert**
keyword followed by a predicate and terminated with a semicolon, as in 
the following example.

```
// openjml -esc T_assert1.java

public class T_assert1 {

  public void example(int i) {
    int neg;
    if (i > 0) {
      neg = -i;
    } else {
      neg = i;
    }
    //@ assert neg <= 0;
  }
}
```

The above example verifies with OpenJML, but the following variation does not:

```
// openjml -esc T_assert2.java

public class T_assert2 {

  public void example(int i) {
    int neg;
    if (i > 0) {
      neg = -i;
    } else {
      neg = i;
    }
    //@ assert neg < 0;
  }
}
```

produces

```
T_assert2.java:12: verify: The prover cannot establish an assertion (Assert) in method example
    //@ assert neg < 0;
        ^
1 verification failure
```

because if `i` is 0, then `neg` is 0 and the assert fails.
In this second example, which is at fault: the code or the assert statement?
Well, that depends on what the intent of the method is: should `neg` be a 
negative number or a non-positive number? The verifier can only identify
the discrepancy between the code and the specification, giving the 
software writer the opportunity to consider the problem and make an
appropriate correction.

Java has its own `assert` statement. By default, the Java assert 
statements are ignored at runtime, unless explicitly enabled.
When enabled (cf. the Java `-ea` or `-esa` runtime option) a Java program will
throw an `AssertionError` if the predicate in the Java assert statement
is false.

OpenJML will interpret a Java `assert` statement in the same way that it
does a JML `assert` statement; it issues a verification error if it 
cannot prove the designated predicate true. So this example, like the 
example above,

```
// openjml -esc T_assert3.java

public class T_assert3 {

  public void example(int i) {
    int neg;
    if (i > 0) {
      neg = -i;
    } else {
      neg = i;
    }
    assert neg < 0; // A Java assert statement (but interpreted by JML)
  }
}
```

produces similar output:

```
T_assert3.java:12: verify: The prover cannot establish an assertion (Assert) in method example
    assert neg < 0; // A Java assert statement (but interpreted by JML)
    ^
1 verification failure
```


<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

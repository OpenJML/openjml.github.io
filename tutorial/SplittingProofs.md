---
title: JML Tutorial - Splitting up proofs
---

By default, OpenJML attempts to verify each method on its own and converts the entire method into one verification condition that contains all of the implicit and explicit assertions needs to verify that a method's specification and implementation agree. Treating each assertion individually or even in groups would require duplicating effort within the solver. Solvers are highly engineered for large problems and for speed.

Nevertheless, sometimes it is helpful to break up a method's verification condition into pieces, for understanding, for debugging, or because the method is large. This lesson describes some mechanisms for doing that.

## The halt statement

The halt statement, `//@ halt;`, may be placed anywhere a statement may be placed in a Java program. Its effect is to halt translation of the method at that point. So the resulting verification condition and proof will only contain assertions from the method preconditions and beginning of the body to that point in the body. If the halt statement is in a branch, then other branches will be translated all the way to the end of the method and its postconditions unless they too contain halt statements.

As a result the verification condition is smaller, any proof is quicker, and any debugging effort is focussed on the portion of the program up to that point. Once that portion of the program is correct and understood, the halt statement can be moved further down in the program and the process repeated.
Obviously this is only a debugging technique; in the end, verification must be successful without any halt statements.

Note that one could obtain a similar effect by inserting a `assume false;` statement into the method. This also has the effect that any assertions after
this statement are not considered by the prover. However, it does not have the effect of making the verification condition smaller and its effect is not
as intuitive.

Here is a simple example with some obvious seeded errors:
```
// openjml --esc T_halt1.java
public class T_halt1 {

  //@ ensures \result == 0;
  public int m(int i) {
    if (i >= 0) {
      //@ assert i < 10;
    } else {
      //@ assert i < -10;
    }
    return i;
  }
}
  
```
produces
```
T_halt1.java:9: verify: The prover cannot establish an assertion (Assert) in method m
      //@ assert i < -10;
          ^
T_halt1.java:11: verify: The prover cannot establish an assertion (Postcondition: T_halt1.java:4:) in method m
    return i;
    ^
T_halt1.java:4: verify: Associated declaration: T_halt1.java:11:
  //@ ensures \result == 0;
      ^
T_halt1.java:7: verify: The prover cannot establish an assertion (Assert) in method m
      //@ assert i < 10;
          ^
4 verification failures
```
(The failures are reported in a non-deterministic order.)
Adding two halt statements before the assertions omits both assertions and the postconditions from analysis:
```
// openjml --esc T_halt2.java
public class T_halt2 {

  //@ ensures \result == 0;
  public int m(int i) {
    if (i >= 0) {
      //@ halt;
      //@ assert i < 10;
    } else {
      //@ halt;
      //@ assert i < -10;
    }
    return i;
  }
}
  
```
has no errors.
Removing one halt statement and leaving the other will trigger one of the assertions and the postcondition.
```
// openjml --esc T_halt3.java
public class T_halt3 {

  //@ ensures \result == 0;
  public int m(int i) {
    if (i >= 0) {
      //@ assert i < 10;
    } else {
      //@ halt;
      //@ assert i < -10;
    }
    return i;
  }
}
  
```
produces
```
T_halt3.java:7: verify: The prover cannot establish an assertion (Assert) in method m
      //@ assert i < 10;
          ^
T_halt3.java:12: verify: The prover cannot establish an assertion (Postcondition: T_halt3.java:4:) in method m
    return i;
    ^
T_halt3.java:4: verify: Associated declaration: T_halt3.java:12:
  //@ ensures \result == 0;
      ^
3 verification failures
```

## The split statement and --split option

The halt statement above makes a kind of horizontal cut in the top-to-bottom flow of a method body. In contrast, the `split` statement makes a kind of vertical division. Consider an `if` statement: the logical analysis has to consider both branches; the split statement directs the prover to consider
each branch individually (as if there were a `halt` statement at the beginning of the other branch). The program can be split at several points, by placing a `//@ split;` statement immediately before the relevant control construct:
* split on the two branchs of an `if`
* split on the cases of a `switch` statement (but not a switch expression)
* split on a loop condition
* split on a block specification (see the next section)
* split on a condition

For the last option, the split statement contains a condition: `//@ split <predicate>;` and the split is done assuming the condition is true and false respectively. A method may have multiple `split` statements, which results ina multiplicative number of splits to proove.

Like the `halt` statement, the `split` statement reduces the size of the verification condition. But unlike the `halt` statement, `split` statements may be left in the method, because, so long as each split case verifies, all execution paths will have been properly verified.

Each split of the method body has a alphabetic designator, like 'ABA', which tells which branch of each split encountered is taken. `openjml` can be run with the option `--split=<designators>` where the value of the option is a comma-separated list of such designators; verification is then attempted for just those split combinations, in turn.

Here is a bare-bones example:
```
// openjml --esc --split= --progress --no-show-summary T_split1.java
public class T_split1 {
  //@ ensures i == 2;
  public static int m(int i) {
    boolean p = i > 0;
    //@ split;
    if (p) {
      //@ split;
      switch (i) {
        case 1: break;
        case 2: break;
        default: break;
      }
    } else {
    }
    //@ show p,i;
    return i;
  }
}
```
which produces
```
Proving methods in T_split1
Starting proof of T_split1.T_split1() with prover z3_4_3
Method assertions are validated
T_split1.java:2:Feasibility check #1 - end of preconditions : OK
T_split1.java:2:Feasibility check #2 - at program exit : OK
Completed proof of T_split1.T_split1() with prover z3_4_3 - no warnings
Starting proof of T_split1.m(int) with prover z3_4_3
Proof attempt for split AA
T_split1.m Method assertions are INVALID
T_split1.java:16: verify: Show statement expression p has value true
    //@ show p,i;
             ^
T_split1.java:16: verify: Show statement expression i has value 1
    //@ show p,i;
               ^
T_split1.java:17: verify: The prover cannot establish an assertion (Postcondition: T_split1.java:3:) in method m
    return i;
    ^
T_split1.java:3: verify: Associated declaration: T_split1.java:17:
  //@ ensures i == 2;
      ^
Result of split AA is Not verified
Proof attempt for split AB
Method assertions are validated
T_split1.java:4:Feasibility check #1 - end of preconditions : OK
T_split1.java:4:Feasibility check #2 - at program exit : OK
Result of split AB is Verified
Proof attempt for split AC
T_split1.m Method assertions are INVALID
T_split1.java:16: verify: Show statement expression p has value true
    //@ show p,i;
             ^
T_split1.java:16: verify: Show statement expression i has value 3
    //@ show p,i;
               ^
T_split1.java:17: verify: The prover cannot establish an assertion (Postcondition: T_split1.java:3:) in method m
    return i;
    ^
T_split1.java:3: verify: Associated declaration: T_split1.java:17:
  //@ ensures i == 2;
      ^
Result of split AC is Not verified
Proof attempt for split B
T_split1.m Method assertions are INVALID
T_split1.java:16: verify: Show statement expression p has value false
    //@ show p,i;
             ^
T_split1.java:16: verify: Show statement expression i has value 0
    //@ show p,i;
               ^
T_split1.java:17: verify: The prover cannot establish an assertion (Postcondition: T_split1.java:3:) in method m
    return i;
    ^
T_split1.java:3: verify: Associated declaration: T_split1.java:17:
  //@ ensures i == 2;
      ^
Result of split B is Not verified
Composite result Not verified
Completed proof of T_split1.m(int) with prover z3_4_3 - with warnings
Completed proving methods in T_split1
12 verification failures
```
First a few details:
* We use the `--progress` option so we can see what is happening (always use that option with splits, at least until they are all succdessful)
* The `--split` option ... TODO
* In th scae of a loop, the split statement is put between the loop specification and the loop itself.

Now note that four splits are produced. First there is a split at the if-statement, `A` for the _then_ branch, `B` for the _else_ branch. Then, within the _then_
branch, there is a switch statement with three cases, which will be labeled `A`, `B`, and `C`. So we have four splits with designators, `AA`, `AB`, `AC`, `B`.
OpenJML attempts verification for each of these in turn. 
* Case AA fails; the `show ` statement tells us that the value of `i` is `1`, as we expect.
* Case AB succeeds, so we don't get a counterexample, but we surmise that `i` must be `2`.
* Case AC fails again, now with an `i` that is positive but not `1` or `2`.
* Case B fails, now with some `i` that is non-positive and `p` is false.

We can rerun this for just two of the splits by using the option `--split=AB,B`, giving
```
Proving methods in T_split1
Starting proof of T_split1.T_split1() with prover !!!!
Skipping proof attempt for split 
No matching splits
Completed proof of T_split1.T_split1() with prover !!!! - ERROR
Starting proof of T_split1.m(int) with prover !!!!
Skipping proof attempt for split AA
Proof attempt for split AB
Feasibility check - end of preconditions : OK
Result of split AB is Verified
Skipping proof attempt for split AC
Proof attempt for split B
T_split1.java:16: warning: Show statement expression p has value false
    //@ show p,i;
             ^
T_split1.java:16: warning: Show statement expression i has value ( - 2147483610 )
    //@ show p,i;
               ^
T_split1.java:17: warning: The prover cannot establish an assertion (Postcondition) in method m
    return i;
    ^
T_split1.java:3: warning: Associated declaration
  //@ ensures i == 2;
      ^
Result of split B is Not verified
Composite result Not verified with 2 splits skipped
Completed proof of T_split1.m(int) with prover !!!! - with warnings
Completed proving methods in T_split1
4 warnings
```

## Block specifications

A final way to reduce the size of verification conditions is to use _block specifications_. This is a technique in which specifications, similar to method specifications, are written for a portion of a method body. Schematically,
```
{
    pre-stuff
    //@ requires P
    //@ ensures Q
    {
       block
    }
    post-stuff
}
```
Here the specification summarizes the effect of the statement (usually a block) that immediately follows. This enables OpenJML to break the proof into two pieces: first one in which the specification is verified against the statement:
```
{
    ... symbolically execute pre-stuff
    prove that P holds
    ... symbolically execute block
    prove that Q holds
}
```
And then second we can use the specification to summarize the block and go on to prove any assertions in 'post-stuff':
```
{
    ... symbolically execute pre-stuff
    prove that P holds
    assume that Q holds
    ... symbolically execute post-stuff
}
```

As you can see from the sketches above, the precondition is not really neeeded; it is just like an assert. The important parts are an `assignable` clause saying what is modified in the block and `ensures` and `signals` clauses that say what the effect of the block is. Other method specification clauses may appear in more complex scenarios -- see the OpenJML Users' Guide for more detail.

The statement specification here can be the specification of
* the next single statement
* most commonly, the next single statement which is a block
* or a sequence of statements (in the same scope) bounded by the `//@ begin;` and `//@ end;` JML statements.

The last case is used when the desired sequence of statements is not contained with in a block, is more than one statement, and one cannot modify the code by putting in a pair of braces, or such a pair of braces would change the scope of declarations.

The two pieces of the proof are an obvious case for splitting the proof. In fact that is the default behavior, becuase the main purpose of a statement specificaiton, along with adding some documentation and clarity, is to be able to divide up the proof. However, if you are writing the software and it seems a statement specification is needed, you should probably consider breaking up the method into multiple methods; if you are verifying legacy code that cannot be modified, then a statement specification can be very handy. It is also helpful as a means of separating out a portion of the method body that is very difficult to prove.

Here is a worked example.

TBD


<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

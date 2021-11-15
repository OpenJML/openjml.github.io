# Frame Conditions

The [previous lesson](MethodCalls) described the verification process when 
there are multiple methods that call each other. But that lesson left out
an important consideration: how to specify side-effects of methods.

Consider this example:
```
// openjml -esc -checkFeasibility=none T_frame1.java
public class T_frame1 {

  public int counter1;
  public int counter2;

  //@ requires counter1 < Integer.MAX_VALUE;
  //@ ensures counter1 == 1 + \old(counter1);
  public void increment1() {
    counter1 += 1;
  }

  //@ requires counter2 < Integer.MAX_VALUE;
  //@ ensures counter2 == 1 + \old(counter2);
  public void increment2() {
    counter2 += 1;
  }
  
  public void test() {
    //@ assume counter1 == 0 && counter2 == 0;
    increment1();
    //@ assert counter1 == 1;
    //@ assert counter2 == 0;
  }
}
  
```
which produces
```
T_frame1.java:23: verify: The prover cannot establish an assertion (Assert) in method test
    //@ assert counter2 == 0;
        ^
1 verification failure
```
Note first a new bit of syntax: the `\old` designator. The `increment` methods make a change in state: the value of `counter1` or `counter2` is different after
the method than before and we need a way to refer to their values before and after. The `\old` syntax means to determine the value of the enclosed expression
in the pre-state. that is, the state at the beginning of the method's execution.
`counter1` without the `\old` designator means the value of `counter1` in the
post-state, the state after the method has completed.

Also, why the comparison to `Integer.MAX_VALUE`? That is to avoid warnings about arithmetic overflow. We'll get to that topic [later](ArithmeticModes).

iNow to the point of this lesson. The two increment methods verify OK, but 
what is happening in the test method?
First we assume some values for `counter1` and `counter2`. This is just to give
a concrete starting point.
After calling `increment1`, the value of `counter1` has increased by 1; 
the postcondition of `increment1` says just that and the first assert
statement is readily proved. 

But the second assert statement is not. Why not? `increment1()` does not change
`counter2`. The problem is that the specification of `increment1()` does not say
that `counter2` is unchanged. One solution would be to add an additional 
ensures clause that states that `counter2 == \old(counter2)`. This specification
verifies OK.

But this is not a practical solution. We can't add to `increment1()'s specification a clause stating that every visible variable is unchanged.
Instead we use a *frame condition* whose purpose is to state what memory
locations a method might have modified. There are a variety of names for
the frame clause: traditionally it is `assigns` or `assignable`, but in OpenJML
we can also use the clearer `writes`. Note that `modifies` is also an
(implemented) synonym, but in some tools it has a slightly different meaning,
so its use is not recommended.

The frame condition states which memory locations might be changed by the method at hand. Anything not mentioned is assumed to be unchanged. In fact, a method
is not allowed to *assign* to a memory location (even with the same value) unless it is listed in the frame condition --- this makes the check for violations of the frame condition, whether by tool or by eye, independent of the values computed.

So now our example looks like this:
```
// openjml -esc -checkFeasibility=none T_frame3.java
public class T_frame3 {

  public int counter1;
  public int counter2;

  //@ requires counter1 < Integer.MAX_VALUE;
  //@ writes counter1;
  //@ ensures counter1 == 1 + \old(counter1);
  public void increment1() {
    counter1 += 1;
  }

  //@ requires counter2 < Integer.MAX_VALUE;
  //@ writes counter2;
  //@ ensures counter2 == 1 + \old(counter2);
  public void increment2() {
    counter2 += 1;
  }
  
  public void test() {
    //@ assume counter1 == 0 && counter2 == 0;
    increment1();
    //@ assert counter1 == 1;
    //@ assert counter2 == 0;
    increment2();
    //@ assert counter1 == 1;
    //@ assert counter2 == 1;
  }
}
  
```
which successfully verifies.

A few more details about the memory locations in a frame condition:
* One does not need to list variables that are local to the body of a method;
those are not visible in the specification and they are not part of the 
program state outside of the method.
* The formal arguments of the method are in scope for the frame condition,
just like for the `requires` and `ensures` clauses. The formal arguments \
themselves cannot be changed by a method, but if the are references to objects,
their fields might be written to by a method. So a method `m(MyType q)`
might have a frame condition `writes q.f;` if `f` is a field of `MyType`
that is written to in the body of `m`.
* If there are no side-effects of a method, you can specify a frame condition `writes \nothing;`
* `q.*` for an expression `q` means all fields of q
* `a[i]` for expression `a` and `i` means tha particular array element
* `a[*]` for array expression `a` means all elements of that array
* `a[i..j]` for expressions `a`, `i`, and `j` means the stated range of array elements

If there is no frame condition at all, then a default is used, namely `writes \everything;`--- which means exactly that: after a call of this method, any memory location in the state might have been written to and might be changed. It is very difficult to prove anything about a program that includes a call to a method with such a frame condition. Thus  
*you must include a frame condition for any method that is called within a program*

A shorthand way to say that a method `writes \nothing;` is to designate it `pure`, as in
```
//@ requires ...
//@ ensures ...
//@ pure
public void m() { ... }
```
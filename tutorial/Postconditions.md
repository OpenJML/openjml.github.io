# Postconditions (`ensures` clauses)

A method's specification states what the method does,
and not how it is done. The effect of a method is
stated in its _postcondition_, which is written in an 
_ensures_ clause.

Consider this example of a method that computes the maximum of four int values.

%include 'T_ensures1.java'


The *ensures* clauses just prior to the method declaration states two 
properties that are expected to hold about the result, which is designated
by the keyword `\result`.

* The result must be equal to one of the four inputs.
* The result must be greater than or equal to each of the four inputs.

The body of the function computes this result. Note that the specification
states the properties of the result but does not state how it is computed.
In fact, the same specification could be used with a different implementation:
```
%include "T_ensures1a.java"
```

Now how can we check that the implementation actually implements the specification? That is the (or one) purpose of the OpenJML tool.
If we execute (cf. [Execution](Execution))
`openjml -esc tutorial/T_ensures1.java`
we find that the openjml tool completes with no error messages and a success
error code, indicating that implementation is verified.

Similarly, `openjml -esc tutorial/T_ensures1a.java` indicates that this
second example also verifies.

Now consider a third example:

%include_relative "T_ensures2.java"


Running `openjml -esc tutorial/T_ensures2.java` produces this output (and an error exit code):
```
%include_relative "T_ensures2.out"
```

The error message tells us that the specification and implementation are
not consistent; in particular, the `ensures` clause on line 3 is not satisfied
when the method exits on line 10. Some code inspection reveals that there
is an error in the `if` condition on line 9: it should be `b > d` (as it is in example `T_ensures1.java`).

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


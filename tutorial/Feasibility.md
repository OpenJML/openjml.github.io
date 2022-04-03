---
title: JML Tutorial - Checking Feasibility
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

Deductive verification typically asks the question: are there any legal inputs that would render an implicit or explicit assertion false?  A second question is: are there any legal inputs that cause execution to reach a given point in the program? That is, is the execution path to that point in the program _feasible_?

The question of feasibility can be important for several reasons.
* If there is indeed some infeasible execution path, then any assertions on that path will not be checked. Then a verification attempt can be successful (no verification errors reported), when in fact that success is because _there was nothing to check_ (because that or maybe all execution paths are infeasible). Thus after a successful verification attempt it can be prudent to check feasibility.
* If there are contradictory assumptions (e.g., assume statements or preconditions or invariants) then any point after those assumptions will not be feasible.
For example
```java
{% include_relative T_Feasibility1.java %}
```
produces
```
{% include_relative T_Feasibility1.out %}
```
* When method A calls method B, the verification of method A relies on correct specifications for method B. Consider this example:
```java
{% include_relative T_Feasibility4.java %}
```
Verification without checking feasibility reports no errors. However, when feasibility is checked, a problem is reported with the call of `mm()`. 
```
{% include_relative T_Feasibility4.out  %}
```
The problem here is that the specs of `mm()` say that the method is `pure`, meaning that it changes nothing, but the ensures clause says that `k` is incremented. 
This contradiction results in stopping any verification after the method call. The feasibility check indeed finds this problem.
This example points out the necessity of verifying all methods used in a program before the program can be considered verified. This is particularly relvant to library methods. These may well have specifications, but a typical client of the library will be forced to trust these specifications and will not have the source code to even attempt a verification of the library cmethods the client uses.
* Some branches of the code may be _dead_, that is, are never executed. In fact sometimes one may wish to prove that a branch, such as an error reporting or recovery branch, will not be executed. Feasibility checking can assist in detection of dead code.

All the various places that OpenJML implements feasibility checking are enumerated below. But first, some caveats are in order.
* Feasibility checking can be time-consuming and especially so if the path in question is _not_ feasible. Accordingly, feasibility checking is off by default.
* Feasibility checking only says that some input combination will reach the given program point, not whether all the combinations you expect will reach that point. For example, if a program
has assumptions `i<= 0` and `i >= 0`, it will still be feasible for `x == 0`, but that may not be the programmer's intent.
* If method A calls method B and method B is underspecified, then an execution path may be considered to be feasible, when in reality it is  not.
Remember that when checking method A, only the specifications of B are considered. Look at this example:
```
{% include_relative T_Feasibility2.java %}
```
The command stated at the top of the example checks whether it is possible to reach the `reachable` statement in the program. Indeed, the check runs without complaint, meaning that the program point is indeed reachable. Given that for positive numbers, the `abs` method should just return its input, how can this be? Well,. in verifying method `m` all we see is the specification of `abs`. That specification is _underspecified_. It only says that the output is non-negative, not that it is equal to the input or its negation. Replacing the `reachable` statement with an `unreachable` statement helps us do some debugging:
```
{% include_relative T_Feasibility3.java %}
```
produces
```
{% include_relative T_Feasibility3.out %}
```
which shows that that the verifier thinks that `i` and `j` can be different (the specific values of `i` and `j` may be different from run to run).

So feasibility checking can be useful if these caveats are kept in mind. Feasibility checking is disabled by default and is enabled with the **--check-feasibility** option. The argument of that option is a 
comma-separated list of location identifiers, listed below. In addition there are some common combinations:
* **none** -- turns off any feasibility checking
* **basic** -- turns on just precondition, assert, assume, reachable, exit, halt, and spec
* **all** -- turns on everything
* **debug** -- just for debugging of OpenJML itself

Here are the possible places that can be checked:
* **reachable** -- all points in the method explicitly marked with a `//@ reachable;` statement
* **precondition** -- at the beginning of the method body; checks whether there are contradictions in the preconditions and invariants
* **assert** -- just before each explicit assert statement; if the execution path to the assertion is not feasible, the assertion will never be checked
* **assume** -- just after each explicit assume statement; if the execution path is not feasible, there is something wrong with the predicate being assumed (or something wrong before it)
* **return** -- is every return statement feasible (after computing the return value)
* **throw** -- is every throw statement feasible (after computing the throw expression)
* **if** -- are both branches of the if condition feasible
* **switch** -- are all branches of a switch statement feasible
* **catch** -- at the beginning of each catch block
* **finally -- at the beginning of each finally block
* **spec** --  at the end of every statement spec block
* **call** -- after any call
* **halt** -- at each halt statement
* **loopcondition** -- at the beginning of the loop body
* **loopexit** -- on the exit branch after testing the loop condition
* **exit** - is it possible to exit the program (normally or with an exception)



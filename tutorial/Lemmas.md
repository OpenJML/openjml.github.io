---
title: JML Tutorial - Missing Information
---

Sometimes during verification it seems that all the solver needs is the information to make one additional connecting step in the reasoning,
but it is unable to find that step itself. We could simply add an assumption, but it really is better to add some provable information that will 
enable the solver to complete its proof. In mathematics, a small result, proved separately, that is used as one step in a larger proof is called a _lemma_. In this lesson we describe how to add lemmas into a proof.

Recall that when a method is verified, the solver assumes the preconditions and then proves the postconditions, assuming any program state transformations by  the method implementation. If there is no implementation, then the postconditions are simply proved from the preconditions.
Thus, suppose we write a model method in this form
```
//@ requires P(x,y);
//@ ensures Q(x,y);
//@ pure helper no_state
//@ model public void lemma(T x, U y) {}
```
Then if this method verifies, we have established `\forall T x, U y; P(x,y) ==> Q(x,y)`.
If the terminating `{}` is replaced by just `;`, then the lemma is simply assumed --- no proof is attempted.

Then, if we write code like this
```
   // some code
   //@ set lemma(i,j);
   // more code
```
The call of `lemma(i,j)` will be replaced by `assert P(i,j); assume Q(i,j);`; this in essence is an instantiation of the lemma for the specific values `i` and `j`. This mechanism is an improvement over writing a quantified axiom or assumption, because here we have explicitly instantiated the lemma, saving the 
solver the work of finding an appropriate instantiation for its proof. Of course, we would need to include such a `set` statement each time it was needed. Another advantage is that the code for the lemma can be included in the specifications of the program and proved along with it.

Sometimes one needs a lemma that expresses a mathematical fact that the proof engine can't solve even as a standalone lemma. In that case we can write the lemma just as above, but with a `;` instead of the final `{}`. We still have a statement of the lemma, but no proof is attempted because there is no body of the lemma to prove. In this case the truth of the lemma must be separately established.

Another form is a lemma with a body that consists of a series of `assert` statements that guide the solver through a proof of the lemma.

Here is an example from a client project:
```
{% include_relative LemmaExample.java %}
```

This example uses `use` instead of `set`. The effect is the same except for one important difference.
With `use`, subexpressions in the next statement that match the left-hand-side of the lemma being used are replaced by the right-hand-side.
This is only really essential if the method uses bit-vectors, as in this case, and one wants to avoid proving bit-vector problems.

In this case, without the `use` statement, `fromUnsigned` takes a very long time to prove (because it is being proved with bit-vectors).
However, with the lemma, it proves quickly. Furthermore, the lemma itself proves quickly (even though it uses bit-vectors).
So the lemma is a helpful assumption, but it is also proved in a sound fashion.

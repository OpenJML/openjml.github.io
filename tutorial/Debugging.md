---
title: JML Tutorial - Debugging specifications and proofs
---

You have written some code and some specifications. You run `openjml` and it reports a verification failure. You read your source and specifications and don't wee any problems. You read them again and still don't see problems. You run `openjml` again just to see if the result changes. It doesn't.

What techniques are there to understand proof failures? 

This is an important question, especially since, just as in debugging programs, much more time is spent 
debugging failing proofs than is spent in basking in the glow of a successful proof -- by then you are on to the next challenge. Again, as in traditional debugging of programs, debugging specifications can be difficult and time-consuming. The lessons under this topic will provide you with some techniques that help.

First note that there are different kinds of problems that can lead to a failed proof:
* The specification and implementation really are different. The proof counterexample can provide information about the difference [here](InspectingCounterexamples). It can also help to break up the verification problem [here](SplittingProofs).
* The proof problem is too big for the prover to solve. For this situation there are techniques to split up the verification problem into sections [here](SplittingProofs).
* The prover is missing some vital information that prevents it from making the necessary proof steps. For this situation you can add lemmas or other assumptions [here](Lemmas).

It is worth restating a few points:
* Just because a specification and implementation agree (`openjml` verifies) does not mean that they are correct. They could still be both wrong in the same way compared to what is really desired of the program. Careful human review and understanding of requirements cannot replace either traditional testing or verification, though both of those are necessary in giving confidence in a program's corretness.
* The techniques presented here are largely specific to `openjml`, at least in the details. Each tool and prover has different ways in which it has difficulties, though some general ideas and techniques may translate from one situation to another.
* Start with simple problems, understand them well, and them move on to complex situations.

For serious problems in real situations (i.e., not your course homework) or difficulty understanding how all of this deductive verification works, feel free to contact the tool developers or other experts in softawre verification. For JML and openjml, start with the issues list at [the OpenJML project](https://github.com/OpenJML/OpenJML/issues).


_Last modified: 2022-03-01 19:07:38_

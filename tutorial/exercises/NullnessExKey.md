---
title: JML Tutorial - Exercises - Nullable and non-null values and types
---
# Exercises:
## [Nullness Tutorial](https://www.openjml.org/tutorial/Nullness)

## **Question 1**

(a) The line marked in the `test()` method does not verify because it tries to pass `null` as an argument to the constructor, but both arguments to the constructor are implicitly non-null, because that is the default in JML.

(b) To make the code verify without changing the rest of the program, the line marked "wrong" should be deleted or commented out.

(c) The other option for making the code verify would be to declare both arguments to the constructor as "nullable". This could be done either by using a Java annotation (`@Nullable`) or by using a JML annotation (`/*@ nullable @*/`) on each argument, as well as the declaration of the fields `fst` and `snd`[^1]. 
Note that if one only declares that the constructor's arguments can be null (i.e., are nullable), then the assignments to the fields `fst` and `snd` will be incorrect, as those fields would still be non-null (by default) in JML.

Note also that the assertion in the `test()` method does not have a possibility of dereferencing null, because although the fields might be null, `p` itself cannot be null and is (by default in JML) not null.

## Footnotes

[^1]: An equivalent way to make the arguments and the fields nullable by default would be to use a modifier on the class as a whole, such as `nullable_by_default`, or to use the OpenJML option `--nullable-by-default` when running OpenJML. These would have the same issues as the options discussed in the text.


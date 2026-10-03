---
title: JML Tutorial - Exercises - Syntax
---
# Syntax Exercises Key:
## [Syntax Tutorial](https://www.openjml.org/tutorial/Syntax)

## **Question 1**

The problem is that there are no spaces following the at-signs (`@`) in the annotations, so it is unclear if they are intended as JML annotations or Java annotations. The annotation `/*@nonnull*/` is especially problematic, as JML will interpret it as a Java annotation, since the JML syntax should be `/*@ non_null */` (or `/*@ non_null @*/`).

## **Question 2**
Using `openjml --require-white-space` on the above code makes all of the comments without white spaces (those starting with at-signs (`@`) be treated by JML as Java comments, so `//@requires false;` is considered to be a Java comment and thus has no effect on JML.

## **Question 3**
A fixed version of the `AnnotationSyntax` class puts whitespace after at-signs in the JML annotations. This would look, for example, like the following.

```
public class AnnotationSyntaxAns {

    //@ requires false;
    //@ ensures true;
    public static void test(/* @nonnull */ int[] a) {
        //@ assert false;   // ERROR: condition is false!
    }

    public static void main() {
        int[] arr = new int[1];
        arr[0] = 0;
        test(arr);   // ERROR: precondition failure!
    }
}

If the code above is checked with OpenJML, the call to the method `test` will cause a verification failure, since the [precondition](https://www.openjml.org/tutorial/Preconditions.html) of that method is `false`.

**Learning Objectives:** 
+ Understand the difference between JML annotations and Java comments

## **[Answer Key](SyntaxExKey)**
## **[All exercises](https://www.openjml.org/tutorial/exercises/exercises)**

## Resources
+ [Question 1 Java file](AnnotationSynatx.java) the `AnnotationSyntax` class above.

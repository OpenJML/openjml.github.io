---
title: JML Tutorial - Exercises - Syntax
---
# Syntax Exercises Key:
## [Syntax Tutorial](https://www.openjml.org/tutorial/Syntax)

## **Question 1**

The problem is that there are no spaces before (or after) the at-signs (`@`) in the annotations, so it is unclear if they are intended as JML annotations or Java annotations; in fact, Java will treat them as Java annotations. The annotation `/*@nonnull*/` is especially problematic, as JML will interpret it as a Java annotation, since the JML syntax should be `/*@ non_null */` (or `/*@ non_null @*/`).

## **Question 2**
Using `openjml --require-white-space` on the above code makes all of the comments without white spaces (those starting with at-signs (`@`) be treated by JML as Java comments, so `//@requires false;` is considered to be a Java comment and thus has no effect on JML. The OpenJML tool will also treat the comment `/*@nonnull@*/` as a Java comment and so OpenJML won't complain about that.

## **Question 3**
A fixed version of the `AnnotationSyntax` class puts whitespace after at-signs in the JML annotations. This would look, for example, like the following. (In the code some comments have been added about the expected errors that ESC will flag now.)

```Java
public class AnnotationSyntax {

    //@ requires false;   // ERROR: precondition conjunct is false!
    //@ ensures true;
    public static void test(/* @nonnull */ int[] a) {
        //@ assert false;   // ERROR: condition is false!
    }

    public static void main() {
        int[] arr = new int[1];
        arr[0] = 0;
        test(arr);    // ERROR: precondition failure!
    }
}
```

If the code above is checked with OpenJML, the call to the method `test` will cause a verification failure, since the [precondition](https://www.openjml.org/tutorial/Preconditions.html) of that method is `false`. Furthermore the assertion `false` can't be proven and so will be noted as a verification error. All this shows that OpenJML is working on the example.

**Learning Objectives:** 
+ Understand the difference between JML annotations and Java comments

## Resources
+ [All exercises](exercises)

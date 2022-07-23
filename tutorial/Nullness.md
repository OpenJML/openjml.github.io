---
title: JML Tutorial - Nullable and non-null values and types
---

Whether references to objects are null or not is a highly important property in Java programs and just about every other programming language,
to the point that some languages are including non-nullness as a property of the type of a variable.

JML also allows you to specify whether or not something is allowed to be null. In fact, JML makes it the default that a value of reference type is never null.
Furthermore, Java has introduced *type annotations* (since Java 8), which are annotations on types rather than on declarations.
The switch to type annotations for nullness changes the syntax of JML in ways that might be surprising or at least unfamiliar to long-time JML users.

## Simple uses of non-null and nullable

At the simplest level, declarations of a variable may include the modifiers `non_null` or `nullable`:
```
/*@ nullable */ String s = ...
/*@ non_null */ String ss = ...
```
These declarations mean that wherever `s` is used, it must be taken into account that `s` might be null.
On the other hand, `ss` is specified to never be null. Accordingly, when `ss` is initialized or the target of an assignment, the value it is given must be provably not null. But thereafter the values can be assumed to be non-null. If there is no modifier, the default is non-null.

Instead of these modifiers, one can use the Java annotations `@NonNull` or `@Nullable` (if one imports the package `org.jmlspecs.annotation`).

The above modifiers are applicable to local declarations, field declarations, formal parameter declarations, and method return type declarations.
```diff
! Caveat: the default for local declarations is still under discussion. OpenJML uses the same default as for types in other places.
```

Here is an example. The code
```
{% include_relative T_Nullness1.java %}
```
produces no errors for `has` because `s` is by default non-null, nor for `make`, because the return value of `make` is allowed to be null. But it 
does issue verification errors for both statements in `test` because both `ss` and the result of `make` may be null and the argument of `has`
is not allowed to be null.

## Non_null and nullable as type annotations

The proper understanding of
```
/*@ non_null */ String ss = ...
```
is that the modifier appplies to the type `String`, not to `ss` directly. That is `ss` has type `@NonNull String`.
In fact, as a type annotation, `non_null` can be applied to any use of the type: along with the declarations mentioned above, that includes type names in cast expressions, in instanceof expressions, in type parameters, even as a modifier of a type variable --- in short, anywhere a type name is allowed, it may be modified with a type annotation. 
However, type annotations on types in the extends and implements clauses of a class declaration are meaningless and ignored (except on generic type arguments).

TODO - more examples here

## Type annotations and fully-qualified type names

Java's syntax for type annotations applied to fully-qualified type names is a bit unexpected. One writes
`java.lang.@NonNull String` (rather than the incorrect `@NonNull java.lang.String`).

## Type annotations and arrays

Applying annotations to arrays also requires some peculiar Java syntax. The difficulty is that one must distinguish between non-null array references and non-null array elements. Java stipulates that
```
@NonNull String @Nullable [] s;
```
declares `s` to have the type *possibly null array of non-null String values*. That is the `@NonNull` (or equivalently `/*@ non_null */`) goes with `String`
and the `@Nullable` goes with the array.

## Nullness defaults for arrays
```diff
! Caveat: the nullness default for array elements is still under discussion
```

While non-null is the overall default, that causes a problem for arrays. The standard way to create and initialize an array is this:
```
String[] array = new String[100];
for (int i = 0; i < array.length; i++) array[i] = ...
```
But the constructor for a new array, `new String[100]`, creates an array with null elements. So the type of `array` cannot be `@NonNull String[]`, even if
we would like that to be the type once it is fully intialized.

TODO - more needs to be said here

## Changing the default

As stated above, JML applies a default `non_null` modifier where no `non_null` or `nullable` indication is otherwise given.
This default can be changed. The modifiers `non_null_by_default` or `nullable_by_default`, or their equivalents `@NonNullByDefault` and `@NullableByDefault`, can be applied to
* a method, in which case the given default is applicable to all types named in the method and its specification
* a class, in which case the altered default applies to all types named in the class, recursively (fields and methods and nested classes)

In addition, tools may provide ways to set the global default. OpenJML has command-line options `--nonnull-by-default` and `--nullable-by-default` that set the default for all the files being analyzed. It is generally preferable to use explicit defaults at the class or method level, because using global tool options may affect files (like library specification files) that are expecting the normal non-null default to apply.

For example,
```
{% include_relative T_NullnessDefault.java %}
```
verifies because `s` is a `@NonNull String` so the dereference in `s.hashCode` is OK. But the code
```
{% include_relative T_NullnessDefault2.java %}
```
produces a verification error
```
{% include_relative T_NullnessDefault2.out %}
```
because at the dereference of `s` it cannot be proven that `s` is non-null, because the default for the type in the formal parameter declaration is now `nullable`.

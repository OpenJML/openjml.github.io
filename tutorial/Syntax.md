---
title: JML Tutorial - Syntax
---

JML specifications are written in specially formatted Java comments.
Accordingly, to a Java compiler, the JML text is just comment.

JML text is written in comments that either
* a) begin with `//@` and end with the end of the line, or
* b) begin with `/*@` and end with `*/`. Lines within such a block comment
may have the first non-whitespace characters be a series of `@` symbols,
as in
```java
public class Z {
  /*@ requires x;
    @ ensures y;
    @*/
  void m() { ... }
}
```

Note that (aside from conditional annotations described below) a
Java comment starting with `@` as its very first character is a JML annotation;
anything else is silently considered a Java comment. Thus
```
public class Z {
  // @ ensures P; // ---- NOT JML - whitespace between // and @
  void m() {}
}
```

One pitfall with annotations is the following. Java annotations 
begin with `@` (such as `@Override`). Thus a commented out Java
annotation might well read `//@Override`. But this is interpreted by
JML tools as a JML annotation and will result in error messages.

One way to avoid this ambiguity is to adopt the personal best practice
of 
* (1) always placing a space before the @ when commenting out Java annotations and
* (2) always placing white space after the @ and before the JML keyword.

If you have source text from elsewhere that is not modifiable and that contains
these problematic Java comments, you can also use the `--require-white-space`
option so that Java comments like `//@Override` are ignored and not considered 
erroneous JML annotations. With this option enabled, JML annotations must
be written with white space, such as `//@ ensures...`, 
and not `//@ensures`.

Consecutive JML comments with only whitespace or Java comments between them
are joined together; expressions can run from one to the other.
```
//@ requires P
//@   && Q
         // Need R also
//@   && R;
```

Comments can be conditional, as described below.

JML annotations are one of these types:
* Modifiers. Modifiers are single words, such as `pure`, that are syntactically similar to Java modifiers like `public` and `static`.
* Clauses. A JML clause begins with a keyword, such as `ensures`, followed by
an expression or other information, and ending with a semicolon. The semicolon
is optional if it is just prior to the end of the JML comment.
* Types. JML defines a number of new specification-only types, such as `\real` and `\bigint`.
* Expression tokens. These occur within JML expressions.
They begin with a backslash (e.g., `\result`). They can be either 
single words (like `\result`) or function-like, such as `\old(x)`.

# Advanced topic: Conditional Specifications

JML annotations can be *conditional* upon defining various keys.

Instead of beginning with either `//@` or `/*@`, the `@` may be preceded by
one or more instances of a `+` or `-` followed by a Java identifier.
The identifiers are keys controlling whether the comment is ignored or not.
No whitespace is permitted before the `@`; in fact, if the above syntax
is not followed precisely, the Java comment will be silently just a Java comment and not a JML annotation.

Keys are defined as follows:
* One or more keys can be defined on the command-line using the `--keys` option;
the value of the option is a comma-separated list of identifiers.
* The `ESC` key is defined if `--esc` is the current command option
* The `RAC` key is defined if `--rac` is the current command option
* The `OPENJML` key is defined within the OpenJML tool
* The `KEY` and `KeY` keys are reserved for the KeY tool

A JML comment with some keys present in the comment is used (i.e., not ignored)
if 
* (a) at least one of the keys given with a `+` sign is defined and
* (b) none of the keys with a `-` sign are defined

So positive keys enable a comment and negative keys disable it, with any
negative key overriding any positive ones.

For example, a comment beginning `//-RAC@` will be used for typechecking (--check) and static checking (--esc), but ignored for runtime checking (--rac). A comment beginning `//+ESC@` will only be used when `-esc` is being applied.
The most common use of conditional JML annotations is the first example: to turn off 
non-executable annotations during runtime-assertion checking but leave
them in place for static checking.




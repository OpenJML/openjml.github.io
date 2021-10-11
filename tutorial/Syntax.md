# Syntax

JML specifications are written in specially formatted Java comments.
Accordingly, to a Java compiler, the JML text is just comment.

JML text is written in comments that either
* a) begin with `//@` and end with the end of the line, or
* b) begin with `/*@` and end with `*/`. Lines with such a block comment
may have the first non-whitespace characters be a series of `@` symbols,
as in
```
/*@ requires x;
  @ ensures y;
  @*/
```

Expressions must be contained entirely within one JML comment.

Comments can be conditional, as described in the topic [Conditional Comments](ConditionalComments).

JML annotations are one of these types:
* A modifier. Modifiers are single words, such as `pure`, that are syntactially similar to Java modifiers like `public` and `static`.

* Clauses. A JML clause begins with a keyword, such as `ensures`, followed by
an expression or other information, and ending with a semicolon. The semicolon
is optional if it is just prior to the end of the JML comment.

* Types. JML defines a number of new specification-only types, such as `\resl` and `\bigint`.

* Expression tokens. These occur within JML expressions.
They begin with a backslash (e.g., `\result`). They can be either 
single workds (like `\result`) or function-like, such as `\old(x)`.


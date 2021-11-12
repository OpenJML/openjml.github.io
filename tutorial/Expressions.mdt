# JML Expressions

The earlier lessons on pre- and post-conditions, assert and assume
stastements all showed examples of *expressions* used in JML clauses.
These expressions look very much  like Java expressions.
Indeed, the JML expression syntax includes all of the Java expression
syntax, with this exception: JML expressions are not allowed to have
side-effects. So the `++`, `--`, and _op_`=` (e.g., `+=`) operators are
not allowed in JML expressions. The meaning of Java operators in 
JML is also unchanged, except for two matters:
* consideration of [arithmetic modes](ArithmeticModes))
* [well-definedness](WellDefinedExpressions)

But JML also adds to Java some new operators and expression syntax. The new operators are these:

* `==>` (implication): this binary operator takes two boolean operands, e.g., `p` and `q`; `p ==> q` is read a "p implies q" and means the same as logical implication, that is, the same as "not p or q". The implication operator has lower 
precedence than `&&` and `||`, so `p && q ==> r || s` means
`(p && q) ==> (r || s)`. `==>` is *right* associative, so that
`p ==> q ==> r` means `p ==> (q ==> r)`, which is the same as `(p && q) ==> r`.
* `<==>` (equivalence): this is also a binary operation between boolean values.
`p <==> q` means the same as `p == q`, except that `<==>` has lower precedence than `&&` and `||`, whereas `==` has higher precedence. 
Thus `p && q == r || s` means (p && (q == r)) || s`, whereas
`p && q <==> r || s` means `(p && q) <==> (r || s)`. i
Also `<==>` is left associative (`p <==> q <==>r` is `(p <==> q) <==> r`, 
though (a) the meaning is the same as if it were right associative and (b) 
expressions that rely on associativity of `<==>` tend to be confusing are should be avoided.
* `<=!=>` (inequivalence): this operator is simply the negation of `<==>`
and has the same precedence as `<==>`.  `<=!=>` is left associative:
`p <=!=> q <==> r` is `(p <=!=> q) <==> r`, though again, expressions relying on associativity of `<=!=>` and `<==>` tend to be confusing and should be avoided.

These operators are described in later tutorial lessons:

* [quantified expressions](QuantifiedExpressions), e.g., **forall*, **exists*
* `<:` [subtype](SubtypeOperator)
* `<#` `<#=` [lock ordering](LockOrdering)

Finally, there are many keywords that diesgnate either singleton values (e.g. `\result`) or function-like operations (e.g., \typeof(...)`. These will be 
explained as needed in future lessons, although one, `\result`, you have already seen. All JML keywords used within expressions begin with a backslash, so they
cannot conflict with Java identifiers.

# JML Expressions

The earlier lessons on pre- and post-conditions, assert and assume
stastements all showed examples of *expressions* used in JML clauses.
As expresions are a building block for nealry all other JML constructs, 
we include a couple lessons at this point to introduce JLM expressions.

JML expressions look very much  like Java expressions.
Indeed, the JML expression syntax includes all of the Java expression
syntax, with this exception: JML expressions are not allowed to have
side-effects. So the `++`, `--`, and _op_`=` (e.g., `+=`) operators are
not allowed in JML expressions. The meaning of Java operators in 
JML is also unchanged, except for two matters:
* consideration of [arithmetic modes](ArithmeticModes)
* [well-definedness](WellDefinedExpressions)

Note that the non-short-circuiting bvoolean operators `&` and `|` are legal
in both Java and JML, though the short-circuiting versions `&&` and `||`
are much more commonly used in Java because they can be more efficient. In
static reasoning, however, execution efficiency does not matter. 
In static reasoning, `&` and `|` are simpler to reason about, but 
`&&` and `||` are often needed because of [well-definedness considerations](WellDefinedExpressions).

But JML also adds to Java some new operators and expression syntax. The new operators are these:

* `==>` (implication): this binary operator takes two boolean operands, e.g., `p` and `q`; `p ==> q` is read a "p implies q" and means the same as logical implication, that is, the same as "not p or q". The implication operator has lower 
precedence than `&&` and `||`, so `p && q ==> r || s` means
`(p && q) ==> (r || s)`. `==>` is *right* associative, so that
`p ==> q ==> r` means `p ==> (q ==> r)`, which is the same as `(p && q) ==> r`.
* `<==>` (equivalence): this is also a binary operation between boolean values.
`p <==> q` means the same as `p == q`, except that `<==>` has lower precedence than `&&` and `||`, whereas `==` has higher precedence. 
Thus `p && q == r || s` means `(p && (q == r)) || s`, whereas
`p && q <==> r || s` means `(p && q) <==> (r || s)`.
Also `<==>` is left associative (`p <==> q <==>r` is `(p <==> q) <==> r`), 
though (a) the meaning is the same as if it were right associative and (b) 
expressions that rely on associativity of `<==>` tend to be confusing and should be avoided.
* `<=!=>` (inequivalence): this operator is simply the negation of `<==>`
and has the same precedence as `<==>`.  `<=!=>` is left associative:
`p <=!=> q <==> r` is `(p <=!=> q) <==> r`, though again, expressions relying on associativity of `<=!=>` and `<==>` tend to be confusing and should be avoided.

Another important addition to JML is the *chaining* of relational operators.
Instead of writing `i <= j && j < k`, one can write `i <= j < k`. Similarly
`i > j > k` means `i > j & j > k`. `<` and `<=` can be chained together and
`>` and`>=` can be chained together, but the two groups cannot be mixed.
Furthermore, `==` does not chain and in fact has a lower precedence than the 
relational operators: `a < b = c < d` means `(a < b) == (c < d)` in both Java and JML. These chained operations are particularly convenient for writing
ranges of indices. For example, for an array `a` one might constrain an index variable `i` as `0 <= i < a.length`.

These additional JML operators are described in later tutorial lessons:

* [quantified expressions](QuantifiedExpressions), e.g., **forall*, **exists*
* `<:` [subtype](SubtypeOperator)
* `<#` `<#=` [lock ordering](LockOrdering)

Finally, there are many keywords that designate either singleton values (e.g. `\result`) or function-like operations (e.g., `\typeof(...)`. These will be 
explained as needed in future lessons, although one, `\result`, you have already seen. All JML keywords used within expressions begin with a backslash, so they
cannot conflict with Java identifiers.

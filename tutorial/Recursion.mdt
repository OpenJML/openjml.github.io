---
title: JML Tutorial - Reasoning about recursive functions and data structures
---
<i>Last Modified: <script type="text/javascript"> document.write(new Date(document.lastModified).toUTCString())</script></i>

This lesson illustrates modeling and reasoning about a recursive data structure with a commented example.

## Singly-linked list example

The example ([List.java](List.java)) is a standard singly-linked list and is included inline [at the end of this lesson](#example-code) (as well as in the 
collection of tutorial examples). The implementation consists of an anchor class `List<W>` that contains
a linked sequence of `Value<W>` node, each with a field of type `W` containing the value. 
The links from the anchor to the head of the list and from node to node in the list are through
`next` fields, typed as `Value<W>`. Both `List` and `Value` derive from a parent class `Link` that declares
the common `next` field and other common functionality. The anchor is not part of the abstract list; it serves as the 
singly-linked list object even when the list is empty.

This example contains a few typical methods: create an empty list, push a new value on the head of the list, pop the first
value off the list, and remove the n'th value in the list.

The abstract value of the `List` is modeled as a JML sequence, `seq<W>`, which is a sequence of all of the `W` values in
the list. 

There are many points to note about the specification of this data structure; we will walk through them in detail.

**Model fields**

We represent the private implementation as a few model fields. In this example we model the size and the sequence of values in the list.
For the latter, we use the built-in JML value type `seq<W>`.

* Let's start with the size of the list. It is represented by the model field `size` (in `Link`), meaning the number of nodes
in the linked list after the current node. The model field is connected to the implementation by a `represents` clause, 
which gives a typical recursive definition of the size of the list.
```
    //@ model public \bigint size; 
    //@ public represents size = ((next == null) ? 0 : 1 + next.size);
```
Note that the type of `size` is the JML type `\bigint`, so we don't have to worry about overflowing some upper bound on the size.
* The abstract representation of the value of the list is the model field `values`, which is a JML `seq<W>`; it is a sequence
of all the values in the list:
```
    //@ model public seq<V> values; // sequence of values after the current Link, not including the current Link
    //@ public represents values = next == null ? seq.<V>empty() : next.values.prepend(next.value);
```
* That values model field is connected to the implementation by its JML `represents` clause (also in `Link`). This is a recursive definition
that defines the value of `values` for a given `Value` node as the concatenation of the `value` of the _next_ node and the `values`
sequence of that _next_ node (which represents the rest of the list after the _next_ node). Moving all the way back to the 
anchor, the `values` field of the anchor is the sequence of value fields beginning with its `next` node, which is the abstract value of the
list. The reason for the `values ` field representing the sequence of value fields after the current node is that then the same definition
can be used for the anchor, which is not part of the abstract list.
* Next it is illustrative to have a `links` model field that is a sequence of all the `Link` objects that make up the linked list.
It is defined by a `represents` clause in the same way as the others.
* The (public) specifications are written in terms of these model abstractions. The model abstractions are connected to the implementation
through the `represents` clauses. So when the implementation performs some computation or makes some state change
using the program's concrete fields, the verifier
checks that the same change is represented in the abstractions, using the represents clauses as definitions. Examples of this are
shown in the discussion of methods below.

**Datagroups**

* Model fields also serve as _datagroups_. Datagroups represent collections of concrete implementation fields so that frame conditions can be abstracted. 
For example, the model field `size` contains all the `next` fields in the list, since any changes to the next fields might change the size of the list.
The `size` datagroup does not contain any of the `value` fields because the values in the sequence do not affect the size, just the number of nodes.
Then a method that changes the size of the list, such as `push`, specifies that it _assigns_ to `size`, which is interpreted to mean that it
might modify any of the concrete fields that are in the `size` datagroup, namely the `next` fields, which indeed it does. If `size` is omitted from
`push`es frame condition or `next` is omitted from `the `size` datagroup, then the verifier will complain that the assignment to `next` in `push` is not allowed.
* A field is declared to be _in_ a datagroup by the `in` clause that is associated with the declaration of that concrete field:
```
    //@ spec_public
    private W value; //@ in values;
    //@ nullable spec_public
    protected List.Value<V> next; //@ in size, values, links; 
    //@ maps next.values \into values; maps next.size \into size; maps next.links \into links;
```
* But in this example, the model fields contain a recursive collection of concrete fields. The specification first declares that `next` is `in` `size`.
But then also, using the `maps` clause it declares the `next.size` is also in `size` (that is, in `this.size`). The effect is  that `n.size` for node `n`,
as a datagroup, contains all the `next` fields after `n` in the linked list. Thus `size` for the anchor contains all the `next` nodes in the list.
* Accordingly then, if we specify that `this.size` might be assigned in a method, assignments to the `next` fields of any of the nodes after `this` are permitted.
And indeed it is just ithis set of fields on which the (abstract) value of `size` depends.
* The other model fields, `values` and `links` (and `ownerFields, which we will get to later), have similar definitions as datagroups.

**Specifications of each method**

A point should be made at the outset. You will see quite a number of `assert` statements in the bodies of methods. There are two reasons for these.
The first is just illustrative: showing what kinds of deductions can be made at each point in the program body. The second is that 
some (not all) of these asserts
serve as lemmas: the system proves each one, and that deduction helps its proof of later assertions or postconditions.
It is part of ongoing work to reduce the number of situations in which such assert-statements-as-lemmas are needed. They are more commonly needed
for recursive model field and methods, so some help in appropriate unrolling is likely needed.

* **List constructor**: This constructor is private becuse it is just used as an aid to the `empty` method. It has a straightforwad specification
that states that its fields are set correctly. Because it only assigns to its own fields, it is `pure`. Because it neither relies on nor ensures
the class's invariants it is declared `helper`.

* **empty**: Creates an empty list. The specification states that by saying that its size is 0 and that `values` and `links` are empty sequences.

* **push**: Adds a new value, in a new node, to the head of the list. The specification expresses this by ensuring appropriate changes in the
model abstractions, like `size` and `values`. Note that the frame condition (`assigns` clause) states that `size`, `values`, and `links` might all be changed.
For the purpose of illustration, this specification is divided into a public and a private part. The public part states the specification in terms of
public abstract values; the private part states what happens to private, implementation fields. In contrast, other methods in this class combine all of the
specification into one public specification case; it can do that because the private implementation fields are declared `spec_public`, meaning that they
are allowed to be mentioned in public specifications. Any client using `push` and having only public visibility to `push` will only see the public
specification of `push`.

* **pop**: Removes the first value from the list, by removing the first node. The specification of `pop` is analogous to that of `push`. One difference is that `pop`
has a precondition stating that you are not allowed to pop anything from the list if the list is empty.

* **remove**. Removes the nth item from the list. This method is declared in `Link` rather than in `List` because it is a recursive method and must be 
declared for `Value` as well as `List`. Rather than repeating an identical implementation and specification, the declaration was placed in the parent class.
The implementation simply recurses through the list, counting down until it reaches the node before the node it is supposed to remove. It then removes that node
and does not propagate further into the list. Thus each recursive call has the effect of reducing the length of the list after the current node by 1,
which is what the specification states. The effect of the method on `values` and `links` is more complicated to express (and to prove) and is not included here.

* **Value.Value**: This constructor is also straightforward, except for its precondition. The precondition ... (REVIEW THIS)

* **Link.Link**: This constructor is also straightforward. As it is intended only to be used by its child classes (and not by clients), it is declared 
`protected` (though an inheritable version of `private` would be better). There are two important aspects of its specification. First, the specification says
`normal_behavior`, which states that the constructor does not throw any exceptions. Second, it is `helper`, which tells clients that the constructor does
not establish any invariants.

* **Link.value()**: A classic getter method and its specification.

* **Exceptions**: All the specifications in this example are headed by `normal_behavior`, which states that no exceptions are expected --- any situation in which the implementation could throw an exception is a specification violation.

**Invariants**

The specification also includes a number of _invariants_, properties that are supposed to be always (or nearly always) true of their data structures.
For example, one states that the size of the `values` abstract sequence is always (outside of method bodies) the same as the size of the list. As each
method is proved on its own terms, without knowing what operations have already occurred on the data structure, that proof needs to have a known starting 
point. The method preconditions and the class invariants are useful for stating those properties. Each (non-helper) method can assume them to be true in its
pre-state and then must establish that they are still, or once again, true in the post-state.

**Tests**

Specifications serve two purposes. First they represent the behavior of the implementation they specify and the two need to be proved consistent. But second,
the specification is used by clients that call the method in question. For that purpose, the specification must be strong enough, and organized appropriately, 
so that when used by a client to accomplish some purpose, that use can be verified to behave as expected.

Consequently, test cases that use the method, together with assertions that state what should be provable as a result, are good unit tests of a specification.
In this example the `Test` class contains a number of example tests. The first one proves that a call of `empty` does indeed produce a zero-length `List`.
`testPushValue` checks that a value pushed is the one retrieved by `value(0)`
The next ones show other algebraic properties: that a `push` and then a `pop` ior `remove(0)` yield the original abstract value for the list.

**Tests: Non-interference**

An important, and sometimes difficult to prove, property of linked, heap-based data structures is whether changes to one structure, such as our linked list, cause changes to another structurem, such as another linked list. Consider tests NI1 and NI2, and imagine a case in which two different List objects each point to the same 
sequence of links and thus have ths ame abstract `values` value. A `push` or a `pop` on one of these lists only affects the anchor element and so the other list
is unaffected, though they still share portions of the same sequence of links. But in test NI3, we are removing a node that is further down the list. Removing
a node in one list definitely affects the other list as well.  Indeed test NI3 cannot be proved without the `owner` structure we will describe shortly.

An even simpler case is test NI4, which asks whether two different lists must have different first nodes. 

One way to reason about such problems is separation logic, which is not currently a part of JML 
(which may limit the kinds of linked structures that JML can effectively specify). But for this example, we can adopt a different approach. 

We declare in each `Link` node an `owner` field. The owner is the `List` anchor node that points to the list. If a node points to its owner, it cannot be part
of two lists. The trick is to specify and prove that the `owner` field reflects our intent.  Note that the `owner` field is a `ghost` field; that is, it is not
part of the implementation. It could as well be, but this gives an opportunity to demonstrate ghost fields.
Along with this ghost field we declare a recursive method that states the following property for each node: I (that is the current node) and each node after me
have the same owner. If this is true for the anchor node as well, and the anchor node has the property that it is its own owner, then all the nodes in that
anchor's list have that anchor as their owner and cannot be part of another list. The property is encapsulated in the model method `allMine`.

We then state this method as an invariant that must always hold for a List. Of course it must be proved that this invariant is maintained by each method.
For example, the `push` method allocates a new node and puts it at the head of the list. It must then be sure to assign the proper value to the ghost `owner`
field. It does this in a `set` statement, which in JML is the means to assign values to ghost variables.

This invariant is the cause of a minor complexity in the specification. The `Link` constructor is a helper constructor so that it does not
have to ensure that this invariant is valid. One could imagine passing into this constructor an appropriate owner value so that a Link can be created with
`owner` already set (and thereby be able to satisfy the invariant). But `owner` is a ghost concept and not part of the implementation; this little proposal would require passing a ghost value in a Java constructor, which we cannot do.

**Datagroups again, and reads clauses**

Along with the `owner` field, we defined a model field `ownerFields`. Model fields like `values` serve as both an abstract value and a datagroup.
As `owner` is a `ghost` field, it is not also a datagroup. So we define `ownerFields` as its datagroup, with built-in type `JMLDatagroup`. It is defined
recursively just like the other datagroups.

This `ownerFields` datagroup is used in the specification of the method `allMine`, discussed above. `allMine` has a reads clause that states what its value
depends on, which in this case is the `owner` and `next` fields.

## Example code

```java
{% include_relative List.java %}
```

# Visibility modifiers and specifications

Java distinguishes four categories of visibility of declarations: public, protected, package, and private.
For example, within a class, all names, even private ones, declared in that class are visible.
But names private to one class are not visible outside that class.

Specifications have a visibility also. Typically a method specification has the same
visibility as the method declaration. That way a client seeing the method declaration
can see its specification also. But if that client is not permitted to see names
with more restricted visibility, then those names should not appear in the specifications either.

For example, this code
```
// openjml --esc T_Visibility1.java
public class T_Visibility1 {
    private int value;

    //@ ensures \result == value;
    public int value() {
        return value;
    }
}
```
violates JML's visibility rules because a client that can see the public declaration of the 
method `value()` does not necessarily have visibility to the private declaration of `value`.
This error results:
```
T_Visibility1.java:5: error: An identifier with private visibility may not be used in a ensures clause with public visibility
    //@ ensures \result == value;
                           ^
1 error
```

So how is one to specify this simple getter method? The simple solution is simply to declare that
the private field is public _for specification purposes_.
The `spec_public` declaration does this:
```
// openjml --esc T_Visibility2.java
public class T_Visibility2 {
    //@ spec_public
    private int value;

    //@ ensures \result == value;
    public int value() {
        return value;
    }
}
```
which now verifies without error.

There is a similar modifier, `spec_protected`, that declares that a declared name has
protected visibility for specification purposes.

But this solution leads easily to simply declaring all names as `spec_public`, which 
obviates the goal of having hidden an implementation in the first place. If an 
implementation is hidden in private declarations, exposed to a client only through
public methods, then we need a specificxiation idiom that respects that.

That is one purpose of model fields, which are preented in the [next lesson](ModelFields).
But here we'll repeat our example using a model field.

```
// openjml --esc T_Visibility3.java
public class T_Visibility3 {
    private int value; //@ in _value;


    //@ public model int _value;
    //@ private represents _value = value;


    //@ ensures \result == _value;
    public int value() {
        return value;
    }
}
```
The general point is this. The model field `_value` _models_ the state of the class object,
as a public abstraction. The `represents` clause, which is private, tells how the abstraction
relates to concrete (private) fields. The specificaiton of `value()` only uses the public
abstraction `_value`. Of course, in this case, the abstraction is quite trivial. In fact,
the goal of the private `value` field is not so much implementation hiding but preventing
access to the data field, that is, not allowin clients to modify `value` directly.
So for simple cases like this the `spec_public` modifier is perfectly fine; in fact, it is
syntactic sugar for the solution in terms of a model field.

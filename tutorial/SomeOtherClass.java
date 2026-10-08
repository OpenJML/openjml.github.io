// openjml --esc SomeOtherClass.java
// This is to be used by SomeClass.java as an auxilliary class
public class SomeOtherClass {
    //@ assignable \nothing;
    public void doSomething(SomeClass t) {
        return;
    }
}

// openjml --esc T_Visibility1.java
public class T_Visibility1 {
    private int _value;

    //@ ensures \result == _value; // ERROR: can't use _value in public spec.
    public int value() {
        return _value;
    }
}

// openjml --esc T_Visibility1.java
public class T_Visibility1 {
    private int _value;

    //@ ensures \result == _value;
    public int value() {
        return _value;
    }
}

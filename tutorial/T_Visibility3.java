// openjml --esc $@
public class T_Visibility3 {
    private int value; //@ in _value;


    //@ public model int _value;
    //@ private represents _value = value;


    //@ ensures \result == _value;
    public int value() {
        return value;
    }
}

// openjml --esc $@
public class T_Visibility3 {
    private int _value; //@ in value;


    //@ public model int value;
    //@ private represents value = _value;


    //@ ensures \result == value;
    public int value() {
        return _value;
    }
}

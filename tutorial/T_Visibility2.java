// openjml --esc $@
public class T_Visibility2 {
    //@ spec_public
    private int value;

    //@ ensures \result == value;
    public int value() {
        return value;
    }
}

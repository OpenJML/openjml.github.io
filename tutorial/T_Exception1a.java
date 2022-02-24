// openjml --esc T_Exception1a.java
//@ nullable_by_default
public class T_Exception1a {

    public static class V {
        public int value;
    }

    //@ requires true;
    //@ ensures \result == v.value;
    //@ signals (NullPointerException e) v == null;
    public int value(V v) {
        return v.value;
    }
}

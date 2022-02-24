// openjml --esc T_Exception1.java
//@ nullable_by_default
public class T_Exception1 {

    public static class V {
        public int value;
    }

    //@ requires true;
    //@ ensures \result == v.value;
    //@ signals (NullPointerException e) v == null;
    //@ signals_only RuntimeException;
    public int value(V v) {
        return v.value;
    }
}

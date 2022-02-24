// openjml --esc T_Exception2.java
//@ nullable_by_default
public class T_Exception2 {

    public static class V {
        public int value;
    }

    //@ requires true;
    //@ ensures \result == v.value;
    //@ signals (Exception e) false;
    public int value(V v) {
        return v.value;
    }
}

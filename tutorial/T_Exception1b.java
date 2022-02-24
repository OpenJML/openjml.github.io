// openjml --esc T_Exception1b.java
//@ nullable_by_default
public class T_Exception1b {

    public static class V {
        public int value;
    }

    //@ requires true;
    //@ ensures \result == v.value;
    //@ signals (NullPointerException e) v == null;
    //@ signals_only \nothing;
    public int value(V v) {
        if (v == null) throw new NullPointerException();
        return v.value;
    }
}

   

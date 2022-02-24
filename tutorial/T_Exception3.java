// openjml --esc T_Exception3.java
//@ nullable_by_default
public class T_Exception3 {

    public static class V {
        public int value;
    }

    //@ requires v != null;
    //@ ensures \result == v.value;
    //@ signals (Exception e) false;
    public int value(V v) {
        return v.value;
    }
}

   

// openjml --no-show-summary --esc T_Maybe.java
public class T_Maybe {

    //@ requires o != null;
    /*@ non_null @*/ Object fetch(/*@ nullable @*/ Object o) {
        return o;
    }

    // ensures \result <==> o == null;
    boolean isNull(/*@ nullable @*/ Object o) {
        return o == null;
    }
}

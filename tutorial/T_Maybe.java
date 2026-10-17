// openjml --esc T_Maybe.java
public class T_Maybe {

    /*@ non_null @*/ Object fetch(/*@ nullable @*/ Object o) {
        //@ assume o != null;
        return o;
    }

    boolean isNull(/*@ nullable @*/ Object o) {
        return o == null;
    }
}

// openjml --esc ObjPair.java
public class ObjPair {
    private /*@ spec_public @*/ Object fst, snd;

    //@ requires f != s;
    //@ ensures fst == f && snd == s && fst != snd;
    public ObjPair(Object f, Object s) {
        fst = f;
        snd = s;
    }

    public static void test() {
        Integer five = Integer.valueOf(5);
        Integer seven = Integer.valueOf(7);
        ObjPair p = new ObjPair(five, seven);
        //@ assert p.fst != p.snd;
        ObjPair op = new ObjPair(null, seven);
    }
}

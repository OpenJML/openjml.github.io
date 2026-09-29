// openjml --esc ObjPairAns.java
public class ObjPairAns {
    private /*@ spec_public nullable @*/ Object fst, snd;

    //@ requires f != s;
    //@ ensures fst == f && snd == s && fst != snd;
    public ObjPairAns(/*@ nullable @*/ Object f, /*@ nullable @*/ Object s) {
        fst = f;
        snd = s;
    }

    public static void test() {
        Integer five = Integer.valueOf(5);
        Integer seven = Integer.valueOf(7);
        ObjPairAns p = new ObjPairAns(five, seven);
        //@ assert p.fst != p.snd;
        ObjPairAns op = new ObjPairAns(null, seven);
    }
}

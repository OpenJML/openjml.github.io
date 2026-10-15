// openjml --esc ObjPair.java
public class ObjPair {
    private Object fst, snd;

    public ObjPair(Object f, Object s) {
        //@ assume f != s;
        fst = f;
        snd = s;
        //@ assert fst == f && snd == s && fst != snd;
    }

    public static void test() {
        Integer five = Integer.valueOf(5);
        Integer seven = Integer.valueOf(7);
        ObjPair p = new ObjPair(five, seven);
        ObjPair oops = new ObjPair(null, seven); // <-- ERROR: this line wrong!
    }
}

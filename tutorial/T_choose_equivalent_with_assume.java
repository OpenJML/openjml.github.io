// openjml --esc T_choose_equivalent_with_assume.java
public class T_choose_equivalent_with_assume {
    public static void test(int k) {
        //@ ghost int j = k;
        //@ assume 1 < j < 4 && 1 < j;
        //@ assert 1 + j <= 4;
        //@ assert 3 <= 1 + j;
    }
}


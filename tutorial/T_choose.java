// openjml --esc T_choose.java
public class T_choose {
    public static void test() {
        //@ assert 1 + (\choose int j; 1 < j < 4; 1 < j) <= 4;
        //@ assert 3 <= 1 + (\choose int j; 1 < j < 4; 1 < j);
    }
}

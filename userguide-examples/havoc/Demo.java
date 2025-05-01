public class Demo {

    public static void main(String... args) {
        int i = 0;
        short s = 0;
        //@ assert i == 0;
        //@ havoc i, s;
        //@ assert Integer.MIN_VALUE <= i <= Integer.MAX_VALUE;
        //@ assert Short.MIN_VALUE <= s <= Short.MAX_VALUE;
        //@ assert i == 0; // FAILS
    }
}

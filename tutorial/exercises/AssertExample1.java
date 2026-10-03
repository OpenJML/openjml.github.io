// openjml --esc AssertExample1.java
public class AssertExample1 {

    public void max(int a, int b, int c) {
        int max;

        if (a >= b && a >= c) {
            max = a;
            // first assert
        } else if (b >= a && b >= c) {
            max = b;
            // second assert
        } else {
            max = c;
        }
        // third assert
    }

}

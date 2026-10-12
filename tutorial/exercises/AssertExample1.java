// openjml --esc AssertExample1.java
public class AssertExample1 {

    private int max;

    public void max3(int a, int b, int c) {
        if (a >= b && a >= c) {
            max = a;
            // first assert here
        } else if (b >= a && b >= c) {
            max = b;
            // second assert here
        } else {
            max = c;
        }
        // third assert here
    }

}

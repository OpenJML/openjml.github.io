// openjml --esc AssertExample1Ans.java
public class AssertExample1Ans {

    private int max;

    public void max3(int a, int b, int c) {
        if (a >= b && a >= c) {
            max = a;
            // first assert here
            //@ assert max >= a && max >= c && max == a;
        } else if (b >= a && b >= c) {
            max = b;
            // second assert here
            //@ assert max >= a && max >= b && max == b;
        } else {
            max = c;
        }
        // third assert here
        //@ assert max >= a && max >= b && max >= c && max == a || max == b || max == c;
    }

}

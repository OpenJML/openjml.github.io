// openjml --esc AssertExample1Ans.java
public class AssertExample1Ans {

    private /*@ spec_public @*/ int max;

    //@ ensures max >= a && max >= b && max >= c;
    public void max(int a, int b, int c) {
        if (a >= b && a >= c) {
            max = a;
            // first assert
            //@ assert max >= a && max >= c;
        } else if (b >= a && b >= c) {
            max = b;
            // second assert
            //@ assert max >= a && max >= b;
        } else {
            max = c;
        }
        // third assert
        //@ assert max >= a && max >= b && max >= c;
    }

}

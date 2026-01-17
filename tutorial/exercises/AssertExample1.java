public class AssertExample1 {

    public void max(int a, int b, int c) {
        int max;

        if (a >= b && a >= c) {
            max = a;
            // first assert
            //@ assert max >= a;
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
// openjml --esc WellDefinedExample1Ans.java
public class WellDefinedExample1Ans {
    /** Stub for a method that returns the index of key in array a. **/
    public int indexOf(int[] a, int key) {
        //@ assume 0 < a.length;
        //@ assume a[0] == key;    // ERROR: some problem with this assume!
        return 0;
    }
}

// openjml --esc AssumeExample1Ans.java
public class AssumeExample1Ans {
    public int[] reverseArray(int[] a) {
        //@ assume 0 < a.length;
        int len = a.length;
        int[] b = new int[len];

        for (int i = 0; i < a.length; i++) {
            //@ assume 0 <= i && i < a.length;
            //@ assume 0 <= len-1 && len-1 < b.length;
            b[len-1] = a[i];
            len--;			
        }
        //@ assert b.length == a.length;
        return b;
    }
}

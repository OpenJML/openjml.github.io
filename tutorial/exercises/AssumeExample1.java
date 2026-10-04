// openjml --esc AssumeExample1.java
public class AssumeExample1 {
    public int[] reverseArray(int[] a) {
        //@ assume 0 < a.length;
        int len = a.length;
        int[] b = new int[len];
        
        for (int i = 0; i < a.length; i++) {
            // first assume here (or both combined)
            // second assume here
            b[len-1] = a[i];
            len--;			
        }
        //@ assert b.length == a.length;
        return b;
    }
}

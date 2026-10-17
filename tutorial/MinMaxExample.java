// openjml --esc MinMaxExample.java
public class MinMaxExample {

    //@ spec_pure
    public int minOfPosArray (int[] a) {
        //@ assume 0 < a.length;
        //@ assume (\forall int i; 0 <= i < a.length; 0 < a[i]);
        int val = a[0];
        int k;
        for (k = 0; k < a.length; k++) {
            //@ assume 0 <= k < a.length;
            if (a[k] < val) {
                val = a[k];
            }
        }
        //@ assume k == a.length;
        //@ assume (\forall int m; 0 <= m < k; val <= a[m]);
        //@ assume (\exists int n; 0 <= n < a.length; val == a[n]);
        //@ assert val == (\min int m; 0 <= m < a.length; a[m]);
        return val;
    }

    //@ spec_pure
    public int maxOfPosArray (int[] a) {
        //@ assume 0 < a.length;
        //@ assume (\forall int i; 0 <= i < a.length; 0 < a[i]);
        int val = a[0];
        int k;
        for (k = 0; k < a.length; k++) {
            //@ assume 0 <= k < a.length;
            if (val < a[k]) {
                val = a[k];
            }
        }
        //@ assume k == a.length;
        //@ assume (\forall int m; 0 <= m < k; a[m] <= val);
        //@ assume (\exists int n; 0 <= n < a.length; val == a[n]);
        //@ assert val == (\max int m; 0 <= m < a.length; a[m]);
        return val;
    }

}

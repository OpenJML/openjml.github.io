// openjml --esc AssumeExample2Ans.java
public class AssumeExample2Ans {
    public int sortFindMax(int[] a) {
        //@ assume a != null; // implicit in JML
        //@ assume 0 < a.length;
        int max;

        //@ maintaining 0 <= i && i <= a.length-1;
        //@ maintaining (\forall int k; 0 <= k < i; a[k] <= a[k+1]);
        //@ maintaining (\forall int l,m; 0 <= l < i < m < a.length; a[l] <= a[m]);
        //@ decreasing a.length - i - 1;
        for (int i = 0; i < a.length-1; i++) {
            //@ assert 0 <= i && i < a.length-1 < a.length;
            //@ assert i+1 < a.length;
            //@ assert (\forall int k; 0 <= k < i; a[k] <= a[k+1]);

            //@ maintaining i < j <= a.length;
            //@ maintaining (\forall int k; 0 <= k < i; a[k] <= a[k+1]);
            //@ maintaining (\forall int l,m; 0 <= l < i < m < a.length; a[l] <= a[m]);
            //@ loop_assigns j, a[i .. ];
            //@ decreasing a.length - j;
            for (int j = i+1; j < a.length; j++) {
                //@ assert 0 <= i < j;
                //@ assert j < a.length;
                if (a[i] > a[j]) {
                    int temp = a[i];
                    a[i] = a[j];
                    a[j] = temp;
                }
                //@ assert a[i] <= a[j];
                //@ assert (\forall int k; 0 <= k < i; a[k] <= a[k+1]);
            }
            //@ assert (\forall int n; i < n < a.length; a[i] <= a[n]);
            //@ assert a[i] <= a[i+1];
            //@ assert (\forall int k; 0 <= k < i; a[k] <= a[k+1]);
        }
        max = a[a.length-1];
        //@ assert (\forall int k; 0 <= k < a.length-1; a[k] <= a[k+1]);
        //@ assert (\exists int l; 0 <= l && l < a.length; a[l] == max); 
        return max;
    }
}

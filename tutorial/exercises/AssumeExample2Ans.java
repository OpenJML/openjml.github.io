// openjml --esc AssumeExample2Ans.java
public class AssumeExample2Ans {
    public int sortFindMax(int[] a) {
        //@ assume a != null;
        int max;

        for (int i = 0; i < a.length-1; i++) {
            for (int j = i+1; j < a.length; j++) {
                //@ assume 0 <= i < a.length;
                //@ assume 0 <= j < a.length;
                if (a[i] > a[j]) {
                    int temp = a[i];
                    a[i] = a[j];
                    a[j] = temp;
                }
            }
        }
        //@ assume (\forall int i; 0 < i < a.length; a[i-1] <= a[i]);
                
        //@ assume 0 <= a.length-1 < a.length;
        max = a[a.length-1];
        //@ assume (\exists int l; 0 < l < a.length; a[l] <= max); 
        //@ assert (\exists int m; 0 < m < a.length; a[m] <= max);
        //@ assert (\forall int k; 0 < k < a.length; a[k-1] <= a[k]);
        return max;

    }
}

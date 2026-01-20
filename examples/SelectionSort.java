// This example was written by Viktorio S. el Hakim - 1/2021
// It establishes that the array is sorted, but not that it is a permutation of the input array

public class SelectionSort {    
    /*@
        assigns arr[*];
        ensures \forall int k; 0 <= k && k < arr.length-1; arr[k] >= arr[k+1];
    @*/
    // Sorts the array in-place from maximum down to minimum
    public static void sort(int /*@ non_null @*/ [] arr) {
        //@ ghost final int n = arr.length;
        
        //@ loop_invariant 0 <= i <= n; // Bounds check
        //@ loop_invariant \forall int j; 0 <= j < i; // Sorted up-to i
        //@                    \forall int k; j < k < n; arr[j] >= arr[k];
        //@ loop_assigns i, arr[*];
        //@ decreasing n-i; // i goes up
        for (int i = 0; i < arr.length; i++) {
            // Sorted sublist is from 0 up to but not including i
            
            // Find maximum in i .. end
            int ub = arr[i];
            int l = i;
            
            //@ loop_invariant i < j <= n; // Bounds check
            //@ loop_invariant \forall int k; i <= k < j; ub >= arr[k]; // max elem up-to j
            //@ loop_invariant i <= l < j; // max index bounds check
            //@ loop_invariant ub == arr[l]; // max index corresponds to max elem.
            //@ loop_assigns j, l, ub;
            //@ decreasing n-j; // j goes up
            for (int j = i+1; j < arr.length; j++) {
                if (arr[j] > ub) {
                    l = j;
                    ub = arr[j];
                }
            }
            // Maximum is at position l
            
            // assert \forall int k; 0 <= k < i; largest <= arr[k];
            // assert \forall int k; i <= k < n; largest >= arr[k];
            
            arr[l] = arr[i];
            arr[i] = ub;
        }
    }
}

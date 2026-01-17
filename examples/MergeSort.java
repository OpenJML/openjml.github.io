// This example was written by Viktorio S. el Hakim - 1/2021
// It establishes that the array is sorted, but not that it is a permutation of the input array

import java.util.Arrays;

public class MergeSort {    
    /*@ 
      requires arr != null && arr.length > 0; //non-null
      assigns arr[*];
      ensures \forall int k; 0<= k < arr.length; \forall int j; k < j < arr.length; arr[k] >= arr[j];
     @*/
    public static void sort(int [] arr) {
        if (arr.length > 0) {
            sortRec(arr,0,arr.length);
        }
    }
    
    
    /*@ 
      requires 0 <= l < r <= arr.length; // bounds
      requires arr != null; // non-null
      assigns arr[l..r-1];
      ensures \forall int k; l <= k < r; \forall int j; k < j < r; arr[k] >= arr[j];
      measured_by r-l+1;
     @*/
    private static void sortRec(int [] arr, int l, int r) {
        if (l + 1 < r) {
            int mid = l + (r-l)/2;
            sortRec(arr,l,mid);
            sortRec(arr,mid,r);
            merge(arr,l,mid,r);
        }
    }
    
    
    /*@
      requires 0 <= l < m < r <= arr.length && arr.length > 1; //bounds
      requires \forall int k,j; l <= k < j < m; arr[k] >= arr[j];
      requires \forall int k,j; m <= k < j < r; arr[k] >= arr[j];
      assigns arr[l..r-1];
      ensures  \forall int k,j; l <= k < j < r; arr[k] >= arr[j] ;
    @*/
    private static void merge(int /*@ non_null @*/ [] arr, final int l, final int m, final int r) {
        final int [] lCpy = Arrays.copyOfRange(arr, l, m),
                     rCpy = Arrays.copyOfRange(arr,m, r);
            
        //@ assert \forall int k; 0 <= k < lCpy.length; lCpy[k] == arr[k+l];
        //@ assert \forall int k; 0 <= k < rCpy.length; rCpy[k] == arr[k+m];
        
        int l1 = 0, r1 = 0;
        /*@
         loop_assigns i, l1, r1, arr[l..r-1];
         loop_invariant 0 <= l1 <= lCpy.length && 0 <= r1 <= rCpy.length;
         loop_invariant l <= i <= r && i == l+l1+r1;
         loop_invariant \forall int k,j; l <= k < i && l1 <= j < lCpy.length; arr[k] >= lCpy[j];
         loop_invariant \forall int k,j; l <= k < i && r1 <= j < rCpy.length; arr[k] >= rCpy[j];
         loop_invariant \forall int k,j; l <= k < j < i; arr[k] >= arr[j];
         decreasing r - i;
        @*/
        for (int i=l; i < r; i++) {
            if (l1 < lCpy.length && (r1 >= rCpy.length || lCpy[l1] >= rCpy[r1])) {
                arr[i] = lCpy[l1++];
            } else {
                arr[i] = rCpy[r1++];
            }
        }
    }
}

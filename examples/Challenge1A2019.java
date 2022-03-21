// This is Challenge 1A from the 2019 VerifyThis competition

// FIXME _ not fully speced and verified

public class Challenge1A2019 {
    
    //@ public normal_behavior
    //@ requires 2 <= a.length < Integer.MAX_VALUE-1;
    //@ assigns \nothing;
    //@ ensures \result.length <= a.length + 2;
    //@ ensures \result.length > 0; // non-empty
    //@ ensures \result[0] == 0 && \result[\result.length-1] == a.length; // begin-to-end
    //@ ensures \forall int i; 0 <= i < \result.length; 0 <= \result[i] <= a.length; // within-bounds
    // @ ensures \forall int i; 0 < i < \result.length; \result[i-1] < \result[i]; // in order
    //@ ensures \forall int i; 0 <= i < \result.length-1; \forall int j; \result[i] <= j < \result[i+1] - 1; a[\result[i]] < a[\result[i]+1] <==> a[j] < a[j+1]; // monotonic
    // @ ensures \forall int i; 0 <= i < \result.length-1; \result[i+1] < a.length ==> (a[\result[i]] < a[\result[i]+1] <=!=> a[\result[i+1]-1] < a[\result[i+1]]); // maximal
    public int[] findMonotonicCutpoints(int[] a) {
        
        int[] cut = new int[a.length+2];
        cut[0] = 0;
        int lengthcut = 1;
        int x = 0;
        int y = 1;
        int n = a.length;

        //@ loop_invariant lengthcut == \count+1;
        //@ loop_invariant 0 <= x;
        //@ loop_invariant y == x+1;
        //@ loop_invariant y <= n+1;
        //@ loop_invariant lengthcut <= y/2+2;
        //@ loop_invariant cut[0] == 0; // begin-to-end so far
        //@ loop_invariant x == cut[lengthcut-1]; // initial conditions for modified variables
        //@ loop_invariant \forall int i; 0 <= i < lengthcut; 0 <= cut[i] <= x; // within bounds so far
        // @ loop_invariant \forall int i; 0 < i < lengthcut; cut[i-1] < cut[i]; // in order
        //@ loop_invariant \forall int i; 0 <= i < lengthcut-1; \forall int j; cut[i] <= j < cut[i+1] - 1; a[cut[i]] < a[cut[i]+1] <==> a[j] < a[j+1]; // monotonic so far
        // @ loop_invariant \forall int i; 0 <= i < lengthcut-1; cut[i+1] < a.length ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i+1]-1] < a[cut[i+1]]); // maximal to higher index
        //@ loop_modifies x, y, lengthcut, cut[*];
        //@ loop_decreases n - y;
        while (y < n) {
//@ reachable;
        // @ assume \forall int i; 0 <= i < lengthcut-1; cut[i+1] < a.length ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i+1]-1] < a[cut[i+1]]); // maximal to higher index

           boolean increasing = a[x] < a[x+1];
           //@ loop_invariant x < y <= n;
           //@ loop_invariant \forall int j; x <= j < y-1; a[x] < a[x+1] <==> a[j] < a[j+1]; // last segment monotonic so far
           // @ loop_invariant \forall int i; 0 <= i < lengthcut-1; cut[i+1] < a.length ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i+1]-1] < a[cut[i+1]]); // maximal so far
           //@ loop_modifies y;
           //@ loop_decreases n - y;
           while (y < n && ((a[y-1] < a[y]) == increasing)) y = y + 1;
        // @ assert \forall int i; i == lengthcut-1; y < n ==> (a[x] < a[x+1] <=!=> a[y-1] < a[y]); // maximal to higher index
           cut[lengthcut] = y;
        // @ assert \forall int i; i == lengthcut-1; cut[i+1] < a.length ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i+1]-1] < a[cut[i+1]]); // maximal to higher index
           lengthcut++;
           x = y;
           y = x + 1;
//@ reachable;
        }
        if (x < n) {
          cut[lengthcut++] = n;
        }
        int[] newcut = new int[lengthcut];
//@ reachable;
        System.arraycopy(cut, 0, newcut, 0, lengthcut);
        return newcut;
    }
}

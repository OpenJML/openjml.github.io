public class Demo {

  //@ requires 0 <= n < 100;
  //@ ensures \result == n*(n-1)/2;
  public static int test(int n) {
    int sum = 0;
    //@ refining
    //@  assigns sum;
    //@  ensures sum + sum == n*(n-1);
    {
    //@ maintaining 0 <= i <= n;
    //@ maintaining sum + sum == i * (i-1);
    //@ loop_assigns sum;
    //@ decreases n-i;
    for (int i=0; i<n; i++) {
      sum += i;
    }
    }

    //@ assert sum == n*(n-1)/2;
    return sum;
  }
}

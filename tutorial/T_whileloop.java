// openjml --esc T_whileloop.java
public class T_whileloop {

  //@ requires a.length % 2 == 0;
  void alternate(boolean[] a) {
    int k = 0;
    //@ maintaining 0 <= \count <= a.length/2;
    //@ maintaining k == 2*\count && \forall int j; 0 <= j < k; a[j] == (j%2 == 0);
    //@ loop_writes k, a[*];
    //@ decreases a.length - \count;
    while (k < a.length) {
      a[k+1] = false;
      a[k] = true;
      k += 2;
    }
    //@ assert \forall int i; 0 <= i < a.length; a[i] == (i%2 == 0);
  }
}

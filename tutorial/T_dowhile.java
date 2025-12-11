// openjml --esc T_dowhile.java
public class T_dowhile {

  //@ requires 20 < a.length;
  public void test(int[] a) {
    int i = 0;
    //@ maintaining i == \count;
    //@ maintaining 0 <= i <= 10;
    //@ maintaining \forall int k; 0 <= k < i; a[k] == 0;
    //@ loop_writes i, a[*];
    //@ decreases 10-i;
    do {
      a[i] = 0;
      ++i;
    } while (i < 10);
    //@ assert \forall int k; 0 <= k < 10; a[k] == 0;
  }
}

// openjml --esc T_assume1Ans.java
public class T_assume1Ans {

  public int findZeroElement(int[] a) {
    //@ assume (\exists int j; 0 <= j < a.length; a[j] == 0);
    int i = 0;
    while (true) {
      //@ assume (\exists int k; 0 <= i < a.length; a[i] == 0);
      //@ assume 0 <= i < a.length;
      if (a[i] == 0) break;
      //@ assume (\exists int k; 0 <= i < k < a.length; a[k] == 0);
      i++;
    }
    //@ assert 0 <= i < a.length;
    //@ assert a[i] == 0;
    return i;
  }
}

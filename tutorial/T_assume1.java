// openjml --esc T_assume1.java
public class T_assume1 {

  public int findZeroElement(int[] a) {
    int i = 0;
    while (true) {
      //@ assume 0 <= i < a.length;
      if (a[i] == 0) break;
      i++;
    }
    //@ assert 0 <= i < a.length;
    //@ assert a[i] == 0;
    return i;
  }
}

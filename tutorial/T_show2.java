// openjml --esc T_show2.java
public class T_show2 {
  //@ ensures \result >= a && \result >= b && \result >= c && \result >= d;
  //@ ensures \result == a || \result == b || \result == c || \result == d;
  int max(int a, int b, int c, int d) {
    int maxSoFar = a;
    if (b > maxSoFar) maxSoFar = b;
    if (c > maxSoFar) maxSoFar = c;
    if (d > maxSoFar) maxSoFar = c;
    //@ show a, b, c, d, maxSoFar;
    return maxSoFar;
  }
}

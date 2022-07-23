// openjml --esc T_show2a.java
public class T_show2a {
  //@ ensures (\lbl A \result >= a) & (\lbl B \result >= b) & (\lbl C \result >= c) & (\lbl D \result >= d);
  //@ ensures \result == a || \result == b || \result == c || \result == d;
  int max(int a, int b, int c, int d) {
    int maxSoFar = a;
    if (b > maxSoFar) maxSoFar = b;
    if (c > maxSoFar) maxSoFar = c;
    if (d > maxSoFar) maxSoFar = b;
    return maxSoFar;
  }
}

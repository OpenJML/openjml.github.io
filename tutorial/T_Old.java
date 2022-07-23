// openjml --check T_Old.java
public class T_Old {

  //@ requires x > 0 && y > 0;
  //@ old \bigint g = Math.gcd(x,y); // spec from Math library
  //@ ensures \result == g;
  public int myGCD(int x, int y) {
     // some code
     return 0; // placeholder
  }
}

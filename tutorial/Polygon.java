// openjml --esc Polygon.java
interface Polygon {
  //@ model instance public int sides;
  //@ model instance public int longestSide;

  //@ public invariant 0 <= longestSide < 20000;
  //@ public invariant sides >= 3;

  //@ requires longestSide < 10000;
  //@ assigns longestSide;
  //@ ensures longestSide == \old(longestSide) + \old(longestSide);
  public void twice();

  //@ ensures \result == sides; pure
  public int sides();

  //@ ensures \result == longestSide; pure
  public int longestSide();
}
class Square implements Polygon {
  public int side; //@ in longestSide;

  //@ public represents sides = 4;
  //@ public represents longestSide = side;

  //@ requires 0 <= s < 20000;
  //@ ensures side == s && sides == 4;
  public Square(int s) { side = s; }

  // specification inherited
  public void twice() { side = side+side; }

  // specification inherited; cf the represents clause for sides
  public int sides() { return 4; }

  // specification inherited; cf the represents clause for longestSide
  public int longestSide() { return side; }
}
class Test {
  //@ requires polygon.longestSide < 10000;
  public void test(Polygon polygon) {
    int s = polygon.sides();
    int p = polygon.longestSide();
    polygon.twice();
    int ss = polygon.sides();
    int pp = polygon.longestSide();
    //@ assert s == ss;
    //@ assert 2*p == pp;
  }

  public void test2(Polygon polygon) {
    //@ assert polygon.sides() == 4; // NOPE - could be any kind of polygon
  }

  public void test3(Square square) {
    //@ assert square.sides() == 4; // OK
  }

  public void test4(Polygon polygon) {
    if (polygon instanceof Square square) {
      //# assert square.sides() == 4; // OK as well
    }
  }
}

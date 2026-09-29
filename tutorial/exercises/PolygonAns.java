// openjml --esc PolygonAns.java
interface PolygonAns {
  //@ model instance public int sides;
  //@ model instance public int longestSide;

  //@ public invariant sides >= 3;
  //@ public invariant longestSide > 0;

  //@ requires longestSide/2 > 0;
  //@ assigns longestSide;
  //@ ensures longestSide == \old(longestSide)/2;
  public void half();

  //@ ensures \result == sides; spec_pure
  public int sides();

  //@ ensures \result == longestSide; spec_pure
  public int longestSide();
}
class Square implements PolygonAns {
  public int side; //@ in longestSide;

  //@ public represents sides = 4;
  //@ public represents longestSide = side;

  //@ requires s > 0;
  //@ ensures side == s && sides == 4;
  public Square(int s) { side = s; }

  // specification inherited
  public void half() { side = side/2; }

  // specification inherited; cf. the represents clause for sides
  public int sides() { return 4; }

  // specification inherited; cf the represents clause for longestSide
  public int longestSide() { return side; }
}
class Test {
  //@ requires 2 < polygon.longestSide < 10000;
  public void test(PolygonAns polygon) {
    int s = polygon.sides();
    int p = polygon.longestSide();
    polygon.half();
    int ss = polygon.sides();
    int pp = polygon.longestSide();
    //@ assert s == ss;
    //@ assert pp == p/2;
  }

  public void test3(Square square) {
    //@ assert square.sides() == 4; // OK
  }

  public void test4(PolygonAns polygon) {
    if (polygon instanceof Square square) {
      //@ assert square.sides() == 4; // OK as well
    }
  }
}

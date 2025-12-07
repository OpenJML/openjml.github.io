// openjml --esc Polygon3.java
interface Polygon3 {
  //@ model instance public int sides;
  //@ model instance public \datagroup allSides;
  //@ model instance public int longestSide; //@ in allSides;

  //@ public invariant 0 <= longestSide < 20000;
  //@ public invariant sides >= 3;

  //@ requires longestSide < 10000;
  //@ assigns allSides;
  //@ ensures longestSide == \old(longestSide) + \old(longestSide);
  public void twice();

  //@ ensures \result == sides; pure
  public int sides();

  //@ ensures \result == longestSide; pure
  public int longestSide();
}
class Square implements Polygon3 {
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
class Triangle implements Polygon3 {
  public int side1; //@ in longestSide;
  public int side2; //@ in longestSide;
  public int side3; //@ in longestSide;

  //@ public invariant 0 <= side1 && 0 <= side2 && 0 <= side3;
  //@ public invariant side1 <= longestSide && side2 <= longestSide && side3 <= longestSide;

  //@ requires 0 <= s1 < 20000 && 0 <= s2 < 20000 && 0 <= s3 < 20000;
  //@ ensures this.side1 == s1 && this.side2 == s2 && this.side3 == s3;
  public Triangle(int s1, int s2, int s3) { side1 = s1; side2 = s2; side3 = s3; }

  //@ public represents sides = 3;
  //@ public represents longestSide = Math.max(side1, Math.max(side2, side3));
  
  public int longestSide() { return Math.max(side1, Math.max(side2, side3)); }

  public int sides() { return 3; }

  public void twice() { side1 += side1; side2 += side2; side3 += side3; }
}
  
class Test {
  //@ requires polygon.longestSide < 10000;
  public void test(Polygon3 polygon) {
    int s = polygon.sides();
    int p = polygon.longestSide();
    polygon.twice();
    int ss = polygon.sides();
    int pp = polygon.longestSide();
    //@ assert s == ss;
    //@ assert 2*p == pp;
  }

  public void test2(Polygon3 polygon) {
    //@ assert polygon.sides() == 4; // NOPE - could be any kind of polygon
  }

  public void test3(Square square) {
    //@ assert square.sides() == 4; // OK
  }

  public void test4(Polygon3 polygon) {
    if (polygon instanceof Square square) {
      //@ assert square.sides() == 4; // OK as well
    }
  }
}

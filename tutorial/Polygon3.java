// openjml --esc Polygon3.java
interface Polygon3 {
  //@ model instance public int sides;
  //@ model instance public \datagroup allSides;
  //@ model instance public int longestSide; //@ in allSides;

  //@ public invariant sides >= 3;

  //@ assigns allSides;
  //@ ensures longestSide == \old(longestSide)/2;
  public void half();

  //@ ensures \result == sides; pure
  public int sides();

  //@ ensures \result == longestSide; pure
  public int longestSide();
}
class Square implements Polygon3 {
  public int side; //@ in longestSide;

  //@ public represents sides = 4;
  //@ public represents longestSide = side;

  //@ ensures side == s && sides == 4;
  public Square(int s) { side = s; }

  // specification inherited
  public void half() { side = side/2; }

  // specification inherited; cf the represents clause for sides
  public int sides() { return 4; }

  // specification inherited; cf the represents clause for longestSide
  public int longestSide() { return side; }
}
class Triangle implements Polygon3 {
  public int side1; //@ in longestSide;
  public int side2; //@ in longestSide;
  public int side3; //@ in longestSide;

  //@ public invariant side1 <= longestSide && side2 <= longestSide && side3 <= longestSide;

  //@ ensures this.side1 == s1 && this.side2 == s2 && this.side3 == s3;
  public Triangle(int s1, int s2, int s3) { side1 = s1; side2 = s2; side3 = s3; }

  //@ public represents sides = 3;
  //@ public represents longestSide = Math.max(side1, Math.max(side2, side3));
  
  public int longestSide() { return Math.max(side1, Math.max(side2, side3)); }

  public int sides() { return 3; }

  public void half() { side1 /= 2; side2 /= 2; side3 /= 2; }
}
  
class Test {
  //@ requires polygon.longestSide < 10000;
  public void test(Polygon3 polygon) {
    int s = polygon.sides();
    int p = polygon.longestSide();
    polygon.half();
    int ss = polygon.sides();
    int pp = polygon.longestSide();
    //@ assert s == ss;
    //@ assert pp == p/2;
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

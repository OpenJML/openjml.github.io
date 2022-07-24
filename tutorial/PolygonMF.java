// openjml --esc PolygonMF.java
interface PolygonMF {
  //@ model instance public JMLDataGroup allSides;
  //@ model instance public int numSides;

  //@ public invariant 0 <= longestSide() < 20000;
  //@ public invariant sides() >= 3;

  //@ requires longestSide() < 10000;
  //@ old int oldLongest = longestSide();
  //@ assigns allSides;
  //@ ensures longestSide() == oldLongest + oldLongest;
  public void twice();

  //@ public normal_behavior
  //@   reads numSides;
  //@ pure helper
  public int sides();

  //@ public normal_behavior
  //@   reads allSides;
  //@ pure helper
  public int longestSide();
}
class Square implements PolygonMF {
  public int side; //@ in allSides;

  //@ requires 0 <= s < 20000;
  //@   ensures side == s;
  public Square(int s) { side = s; }

  // specification inherited
  public void twice() { side = side+side; }

  //@ also public normal_behavior
  //@   reads numSides;
  //@   ensures \result == 4;
  //@ pure helper
  public int sides() { return 4; }

  //@ also public normal_behavior
  //@  reads allSides;
  //@  ensures \result == side;
  //@ pure helper
  public int longestSide() { return side; }
}
class Test {
  //@ requires polygon.longestSide() < 10000;
  public void test(PolygonMF polygon) {
    int s = polygon.sides();
    int p = polygon.longestSide();
    polygon.twice();
    int ss = polygon.sides();
    int pp = polygon.longestSide();
    //@ assert s == ss;
    //@ assert 2*p == pp;
  }

  public void test2(PolygonMF polygon) {
    //@ assert polygon.sides() == 4; // NOPE - could be any kind of polygon
  }

  public void test3(Square square) {
    //@ assert square.sides() == 4; // OK
  }

  public void test4(PolygonMF polygon) {
    if (polygon instanceof Square square) {
      //# assert square.sides() == 4; // OK as well
    }
  }
}

// openjml --esc PolygonMM.java
public interface PolygonMM {
  //@ model instance public \datagroup allSides;

  //@ public normal_behavior
  //@   reads \nothing;
  //@   ensures \result >= 3;
  //@ spec_pure helper
  public int sides();

  //@ public normal_behavior
  //@   reads allSides;
  //@ spec_pure helper
  public int longestSide();

  //@ public invariant sides() >= 3;

  //@ old int s = longestSide();
  //@ assigns allSides;
  //@ ensures longestSide() == s/2;
  public void half();

}
class Square implements PolygonMM {
  public int side; //@ in allSides;

  //@ public invariant 0 <= side;

  //@ requires 0 <= s;
  //@ ensures side == s;
  public Square(int s) { side = s; }

  // specification inherited
  public void half() { side = side/2; }

  //@ also public normal_behavior
  //@  reads \nothing;
  //@  ensures \result == 4;
  //@ spec_pure helper
  public int sides() { return 4; }

  //@ also public normal_behavior
  //@  requires 0 <= side;
  //@  ensures \result == side;
  //@ spec_pure helper
  public int longestSide() { return side; }
}
class Triangle implements PolygonMM {
  public int side1; //@ in allSides;
  public int side2; //@ in allSides;
  public int side3; //@ in allSides;

  //@ public invariant side1 <= longestSide() & side2 <= longestSide() & side3 <= longestSide();
  //@ public invariant side1 == longestSide() | side2 == longestSide() | side3 == longestSide();

  //@ ensures this.side1 == s1 & this.side2 == s2 & this.side3 == s3;
  public Triangle(int s1, int s2, int s3) { side1 = s1; side2 = s2; side3 = s3; }

  //@ also public normal_behavior
  //@  ensures \result >= side1 && \result >= side2 && \result >= side3;
  //@  ensures \result == side1 || \result == side2 || \result == side3;
  //@ spec_pure helper
  public int longestSide() { return Math.max(side1, Math.max(side2, side3)); }

  //@ also public normal_behavior
  //@   reads \nothing;
  //@   ensures \result == 3;
  //@ spec_pure helper
  public int sides() { return 3; }

  
  public void half() { side1 /= 2; side2 /= 2; side3 /= 2; }
}
  
class Test {

  public void test(PolygonMM polygon) {
    int s = polygon.sides();
    int p = polygon.longestSide();
    polygon.half();
    int ss = polygon.sides();
    int pp = polygon.longestSide();
    //@ assert s == ss;
    //@ assert pp == p/2;
  }

  public void test2(PolygonMM polygon) {
    //@ assert polygon.sides() == 4; // NOPE - could be any kind of polygon
  }

  public void test3(Square square) {
    //@ assert square.sides() == 4; // OK
  }

  public void test4(PolygonMM polygon) {
    if (polygon instanceof Square square) {
      //@ assert square.sides() == 4; // OK as well
    }
  }
}

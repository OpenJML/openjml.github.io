// openjml --esc PolygonMM.java
public interface PolygonMM {
  //@ public normal_behavior
  //@   reads \nothing;
  //@   ensures \result >= 3;
  //@ spec_pure helper
  public int numSides();

  //@ model instance \datagroup allSides;

  //@ public normal_behavior
  //@   reads allSides;
  //@ spec_pure helper
  public int longestSide();

  //@ public invariant numSides() >= 3;

  //@ old int ls = longestSide();
  //@ assignable allSides;
  //@ ensures longestSide() == ls/2;
  public void half();

}

class Square implements PolygonMM {
  //@ also public normal_behavior
  //@  reads \nothing;
  //@  ensures \result == 4;
  //@ spec_pure helper
  public int numSides() { return 4; }

  private int _side; //@ in allSides;

    /*@  public normal_behavior
      @   reads allSides;
      @ also
      @  private normal_behavior
      @   reads _side;
      @   ensures _side == \result;
      @*/
  //@ spec_pure helper
  public int side() {
      return _side;
  }

  //@ public invariant 0 <= side();

  //@ requires 0 <= s;
  //@ ensures side() == s;
  public Square(int s) { _side = s; }

  // specification inherited
  public void half() { _side = _side/2; }

  //@ also public normal_behavior
  //@  requires 0 <= side();
  //@  ensures \result == side();
  //@ spec_pure helper
  public int longestSide() { return _side; }
}

class Triangle implements PolygonMM {
    private int _side1; //@ in allSides;
    private int _side2; //@ in allSides;
    private int _side3; //@ in allSides;

  //@  public normal_behavior
  //@   reads allSides;
  //@ also
  //@  private normal_behavior
  //@   reads _side1;
  //@   ensures \result == _side1;
  //@ spec_pure helper
  public int side1() { return _side1; }

  //@  public normal_behavior
  //@   reads allSides;
  //@ also
  //@  private normal_behavior
  //@   reads _side2;
  //@   ensures \result == _side2;
  //@ spec_pure helper
  public int side2() { return _side2; }

  //@  public normal_behavior
  //@   reads allSides;
  //@ also
  //@  private normal_behavior
  //@   reads _side3;
  //@   ensures \result == _side3;
  //@ spec_pure helper
  public int side3() { return _side3; }

  //@ public invariant side1() <= longestSide() & side2() <= longestSide() & side3() <= longestSide();
  //@ public invariant side1() == longestSide() | side2() == longestSide() | side3() == longestSide();

  //@ ensures side1() == s1 & side2() == s2 & side3() == s3;
  public Triangle(int s1, int s2, int s3) {
    _side1 = s1; _side2 = s2; _side3 = s3;
  }

  //@ also public normal_behavior
  //@  ensures side1() <= \result && side2() <= \result && side3() <= \result;
  //@  ensures side1() == \result || side2() == \result || side3() == \result;
  //@ spec_pure helper
  public int longestSide() { return Math.max(_side1, Math.max(_side2, _side3)); }

  //@ also public normal_behavior
  //@   reads \nothing;
  //@   ensures \result == 3;
  //@ spec_pure helper
  public int numSides() { return 3; }
  
  public void half() { _side1 /= 2; _side2 /= 2; _side3 /= 2; }
}
  
class Test {

  public void test(PolygonMM polygon) {
    int ns = polygon.numSides();
    int p = polygon.longestSide();
    polygon.half();
    int ss = polygon.numSides();
    int pp = polygon.longestSide();
    //@ assert ns == ss;
    //@ assert pp == p/2;
  }

  public void test2(PolygonMM polygon) {
    //@ assert polygon.numSides() == 4; // NOPE - could be any kind of polygon
  }

  public void test3(Square square) {
    //@ assert square.numSides() == 4; // OK
  }

  public void test4(PolygonMM polygon) {
    if (polygon instanceof Square square) {
      //@ assert square.numSides() == 4; // OK as well
    }
  }
}

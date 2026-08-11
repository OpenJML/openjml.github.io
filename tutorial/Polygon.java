// openjml --esc Polygon.java
public interface Polygon {
  //@ model instance public int numSides;

  //@ model instance public \datagroup allSides;

  //@ model instance public int longestSide; //@ in allSides;

  //@ public invariant numSides >= 3;

  //@ old int ls = longestSide;
  //@ assignable allSides;
  //@ ensures longestSide == ls/2;
  public void half();

  //@ ensures \result == numSides; spec_pure
  public int numSides();

  //@ ensures \result == longestSide; spec_pure
  public int longestSide();
}

class Square implements Polygon {
  //@ public model int side; //@ in longestSide;
  private int _side; //@ in side;
  //@ private represents side = _side;

  //@ public represents numSides = 4;
  //@ public represents longestSide = side;
    
  //@ ensures side == s && numSides == 4;
  public Square(int s) { _side = s; }

  // specification inherited
  public void half() { _side = _side/2; }

  // specification inherited; cf. the represents clause for numSides
  public int numSides() { return 4; }

  // specification inherited; cf. the represents clause for longestSide
  public int longestSide() { return _side; }
}

class Triangle implements Polygon {
  //@ public represents numSides = 3;
  //@ public model int side1, side2, side3; //@ in allSides;
  private int _side1; //@ in side1; //@ in longestSide;
  //@ private represents side1 = _side1;
  private int _side2; //@ in side2; //@ in longestSide;
  //@ private represents side2 = _side2;
  private int _side3; //@ in side3; //@ in longestSide;
  //@ private represents side3 = _side3;

  //@ private represents longestSide = Math.max(_side1, Math.max(_side2, _side3));

  //@ public invariant side1 <= longestSide() & side2 <= longestSide() & side3 <= longestSide();
  //@ public invariant side1 == longestSide() | side2 == longestSide() | side3 == longestSide();

  //@ ensures this.side1 == s1 & this.side2 == s2 & this.side3 == s3 && numSides == 3;
  public Triangle(int s1, int s2, int s3) {
      _side1 = s1; _side2 = s2; _side3 = s3;
  }

  //@ also public normal_behavior
  //@  ensures side1 <= \result && side2 <= \result && side3 <= \result;
  //@  ensures side1 == \result || side2 == \result || side3 == \result;
  //@ spec_pure helper
  public int longestSide() {
      //@ check side1 == _side1 && side2 == _side2 && side3 == _side3;
      return Math.max(_side1, Math.max(_side2,_side3));
  }

  //@ also public normal_behavior
  //@   reads \nothing;
  //@   ensures \result == 3;
  //@ spec_pure helper
  public int numSides() { return 3; }

  public void half() { _side1 /= 2; _side2 /= 2; _side3 /= 2; }
}

class Test {
  //@ requires polygon.longestSide < 10000;
  public void test(Polygon polygon) {
    int ns = polygon.numSides();
    int p = polygon.longestSide();
    polygon.half();
    int ss = polygon.numSides();
    int pp = polygon.longestSide();
    //@ assert ns == ss;
    //@ assert pp == p/2;
  }

  public void test2(Polygon polygon) {
    //@ assert polygon.numSides() == 4; // NOPE - could be any kind of polygon
  }

  public void test3(Square square) {
    //@ assert square.numSides() == 4; // OK
  }

  public void test4(Polygon polygon) {
    if (polygon instanceof Square square) {
      //@ assert square.numSides() == 4; // OK as well
    }
  }
}

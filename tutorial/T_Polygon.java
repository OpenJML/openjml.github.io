// openjml --esc T_Polygon.java
public interface T_Polygon {

  /** Number of sides to the polygon */
  //@ ensures \result >= 3;
  //@ pure helper
  public int sides();

}   

class Square implements T_Polygon {

  /** Length of one side of the Square */
  //@ public invariant side >= 0;
  public int side;

  //@ requires 0 <= side < 1000;
  //@ ensures this.side == side;
  public Square(int side) {
    this.side = side;
  }

  //@ also ensures \result == 4;
  //@ pure helper
  public int sides() {
    return 4;
  }

}

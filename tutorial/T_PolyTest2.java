// openjml --esc T_PolyTest2.java T_Polygon.java
public class T_PolyTest2 {

  public void test(T_Polygon poly) {
    if (poly instanceof Square sq) {
      int i = sq.sides();
      //@ assert i > 2; // OK -- property of all T_Polygon instances
      //@ assert i == 4; // OK -- this T_Polygon is a Square
    }
  }
}

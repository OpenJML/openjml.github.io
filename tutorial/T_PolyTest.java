// openjml --esc T_PolyTest.java T_Polygon.java
public class T_PolyTest {

  public void test(T_Polygon poly) {
    int i = poly.sides();
    //@ assert i > 0; // OK -- property of all T_Polygon instances
    //@ assert i == 4; // NO -- who knows what kind of polygon it is
  }

  public void test2(Square sq) {
    int i = sq.sides();
    //@ assert i > 0; // OK - true of all T_Polygon instances
    //@ assert i == 4; // OK - true of Square instances
  }
}

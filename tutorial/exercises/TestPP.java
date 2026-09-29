// openjml --esc TestPP.java
public class TestPP {
    
    public void test() {
        // PositivePoint2 pp = new PositivePoint2(3,4);
        PositivePoint pp = new PositivePoint(3,4);
        pp.setX(-3);
        //@ assert 0 < pp.x;
    }
}

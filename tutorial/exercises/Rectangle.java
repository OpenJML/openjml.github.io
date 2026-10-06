// openjml --esc Rectangle.java
public class Rectangle {

    //@ requires 0 < w;
    //@ requires 0 < h;
    //@ requires w*h <= Integer.MAX_VALUE;
    //@ ensures \result == w*h;
    public int area(int w, int h) {
        return w*h;
    }
    
}

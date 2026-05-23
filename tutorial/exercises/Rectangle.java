public class Rectangle {

    //@ requires w*h <= Integer.MAX_VALUE;
    //@ ensures \result == w*h;
    public int area(int w, int h) {
        return w*h;
    }

}

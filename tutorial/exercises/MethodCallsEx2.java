public class MethodCallsEx2 {

    //@ requires 0 < w && 0 < h && w*h <= Integer.MAX_VALUE;
    //@ requires 0 < materialSqFt;
    //@ ensures \result <==> (areaOfRectangle(w,h) < materialSqFt);
    public boolean enoughMaterial(int materialSqFt, int w, int h) {
        int area = areaOfRectangle(w, h);
        return (area < materialSqFt);	
    }

    //@ requires 0 < w && 0 < h;
    //@ requires w*h <= Integer.MAX_VALUE;
    //@ ensures 0 < \result;
    //@ ensures w <= \result;
    //@ ensures h <= \result;
    //@ ensures \result == w*h;
    //@ spec_pure
    public int areaOfRectangle(int w, int h) {
        int A = w*h;
        return A;
    }	

}

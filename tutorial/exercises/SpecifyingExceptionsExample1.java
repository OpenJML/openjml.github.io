// openjml --esc SpecifyingExceptionsExample1.java
public class SpecifyingExceptionsExample1 {

    //@ ensures \result == arr[index];
    //@ signals (Exception e) false;
    public int elementAtIndex(int[] arr, int index) {
        return arr[index];   // ERROR: index may be out of bounds!
    }
}

// openjml --esc SpecifyingExceptionsExample1Ans.java
public class SpecifyingExceptionsExample1Ans {

    //@ requires 0 <= index < arr.length;
    //@ ensures \result == arr[index];
    //@ signals (Exception e) false;
    public int elementAtIndex(int[] arr, int index) {
        return arr[index];
    }
}

public class PreCondEx1 {

    //@ requires 0 < a.length;
    //@ ensures \result == a[0];
    public int element0(int a[]) {
        return a[0];
    }
}

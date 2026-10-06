// openjml --esc PreCondEx1.java
public class PreCondEx1 {

    public int element0(int a[]) {
        return a[0];   // ERROR: a[0] may not be defined!
    }
}

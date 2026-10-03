// openjml --esc AnnotationSyntax.java
public class AnnotationSyntax {

    //@requires false;
    //@ensures true;
    public static void test(/*@nonnull*/ int[] a) {
        //@assert false;   // ERROR: condition is false!
    }

    public static void main() {
        int[] arr = new int[1];
        arr[0] = 0;
        test(arr);    // ERROR: precondition failure!
    }
}

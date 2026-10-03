// openjml --esc TestOpenJML.java
/** a class to test if OpenJML's ESC is working properly **/
public class TestOpenJML {
    public static void main(String [] argv) {
        System.out.println("running TestOpenJML...");
        //@ assert 1 < 0;   // ERROR: ESC should fail on this!
    }
}
    

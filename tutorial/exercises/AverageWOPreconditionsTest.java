// openjml --esc AverageWOPreconditionsTest.java
public class AverageWOPreconditionsTest {

    public static void main(String [] argv) {
        AverageWOPreconditions av = new AverageWOPreconditions();
        double nan = Double.NaN;
        double res = av.average(2.0, nan);
        System.out.println("Result of calling AverageWOPreconditions.average is: " + res);
    }
}

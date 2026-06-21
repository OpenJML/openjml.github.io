public class AverageTest {

    public static void main(String [] argv) {
        Average av = new Average();
        double nan = Double.NaN;
        double res = av.average(2, nan);
        System.out.println("Result of calling Average.average is: " + res);
    }
}

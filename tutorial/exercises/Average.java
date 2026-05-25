public class Average {

    /*@ ensures Math.abs(\result - (x+y)/2.0) < 0.001; @*/
    public double average(double x, double y) {
        return (x+y)/2.0;
    }
}

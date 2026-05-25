public class Average {

    /*@ requires !Double.isNaN(x);
      @ requires !Double.isNaN(y);
      @ ensures Math.abs(\result - (x+y)/2.0) < 0.001; @*/
    public double average(double x, double y) {
        return (x+y)/2.0;
    }
}

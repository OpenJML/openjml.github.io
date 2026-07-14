// openjml --esc Inches.java
public class Inches {
    private /*@ spec_public @*/ double measure;
    
    //@ requires !Double.isNaN(inches);
    //@ requires 0.0 <= inches;
    public Inches(double inches) {
        measure = inches;
    }

    //@ old double epsilon = 0.1e-9;
    //@ requires !Double.isNaN(oth);
    //@ requires 0.0 <= oth;
    //@ ensures Math.abs(measure - multiple*oth) < epsilon;
    public Inches(double oth, int multiple) {
        measure = multiple * oth;
    }

    public void test() {
        Inches i = new Inches(3.0);
        //@ assert 0.0 <= i.measure;
        Inches f = new Inches(5.0, 12);
        //@ assert 0.0 <= f.measure;
    }
}

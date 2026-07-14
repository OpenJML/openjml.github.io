// openjml --esc InchesAns.java
public class InchesAns {
    private /*@ spec_public @*/ double measure;

    public initially !Double.isNaN(measure);
    public initially 0.0 <= measure;
    
    //@ requires !Double.isNaN(inches);
    //@ requires 0.0 <= inches;
    public InchesAns(double inches) {
        measure = inches;
    }

    //@ old double epsilon = 0.1e-9;
    //@ requires !Double.isNaN(oth);
    //@ requires 0.0 <= oth;
    //@ ensures Math.abs(measure - multiple*oth) < epsilon;
    public InchesAns(double oth, int multiple) {
        measure = multiple * oth;
    }

    public void test() {
        InchesAns i = new InchesAns(3.0);
        //@ assert 0.0 <= i.measure;
        InchesAns f = new InchesAns(5.0, 12);
        //@ assert 0.0 <= f.measure;
    }
}

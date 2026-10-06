// openjml --esc PreCondEx2Wrong.java
public class PreCondEx2Wrong {

    //@ requires !Double.isNaN(balance);
    //@ requires 0.0 <= balance;
    //@ requires !Double.isNaN(price);
    //@ requires 0.0 <= price;
    //@ requires 0 < n;
    public double purchase(double balance, double price, int n) {
        double oldBalance = balance;
	balance = balance - (price*n);
        //@ assert 0.0 <= balance <= oldBalance;   // ERROR: may fail!
	return balance;
    }
}

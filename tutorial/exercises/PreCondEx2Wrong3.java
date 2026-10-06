// openjml --esc PreCondEx2Wrong3.java
public class PreCondEx2Wrong3 {

    //@ requires !Double.isNaN(balance);
    //@ requires 0.0 <= balance;
    //@ requires !Double.isNaN(price);
    //@ requires (price*n) <= balance;
    public double purchase(double balance, double price, int n) {
        double oldBalance = balance;
	balance = balance - (price*n);
        //@ assert 0.0 <= balance <= oldBalance;   // ERROR: may fail!
	return balance;
    }
}

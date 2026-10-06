// openjml --esc PreCondEx2.java
public class PreCondEx2 {

    public double purchase(double balance, double price, int n) {
        double oldBalance = balance;
	balance = balance - (price*n);
        //@ assert 0.0 <= balance <= oldBalance;   // ERROR: may fail!
	return balance;
    }
}

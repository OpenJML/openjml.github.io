// openjml --esc PreCondEx2.java
public class PreCondEx2 {

    //@ ensures \result >= 0.0;
    public double bankUpdate(double bankAccount, double price, int n) {
	bankAccount = bankAccount - (price*n);
	return bankAccount;   // ERROR: may be NaN!
    }
}

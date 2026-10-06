// openjml --esc PreCondEx2Ans.java
public class PreCondEx2Ans {

    //@ requires !Double.isNaN(bankAccount);
    //@ requires bankAccount > 0.0;
    //@ requires !Double.isNaN(price);
    //@ requires price >= 0.0;
    //@ requires (price*n) <= bankAccount;
    //@ ensures \result >= 0.0;
    public double bankUpdate(double bankAccount, double price, int n) {
	bankAccount = bankAccount - (price*n);
	return bankAccount;
    }
}

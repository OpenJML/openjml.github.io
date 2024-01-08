// openjml -esc PreconditionExample1.java
public class PreconditionExample1 {
	
	//@ requires !Double.isNaN(balance);
	//@ requires balance > 0.0;
	//@ requires !Double.isNaN(price);
	//@ requires price >= 0;
	//@ requires balance >= price * n;
	//@ ensures Math.abs(\result - \old(balance-(price*n))) < 0.001;
	//@ ensures \result >= 0.0;
	public double balanceUpdate(double balance, double price, int n) {
		balance = balance - (price*n);
		return balance;
	}

}

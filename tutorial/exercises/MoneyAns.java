// openjml --esc MoneyAns.java
public class MoneyAns {
    private /*@ spec_public @*/ int dollars, cents;

    //@ requires c < 100;
    //@ ensures dollars == d && cents == c;
    public MoneyAns(int d, int c) {
        dollars = d;
        cents = c;
    }

    //@ requires this != m;
    //@ requires cents < 100;
    //@ requires m.cents < 100;
    /*@ ensures \result <==> (this.dollars == m.dollars
      @                        && this.cents == m.cents); @*/
    public /*@ spec_pure @*/ boolean equals(MoneyAns m) {
        return this.dollars == m.dollars && this.cents == m.cents;
    }
        
    //@ requires dollars + cents/100 <= Integer.MAX_VALUE;
    //@ assignable dollars, cents;
    //@ ensures cents < 100;
    public void normalize() {
        if (cents >= 100) {
            dollars += cents/100;
            cents = cents % 100;
        }
    }
}

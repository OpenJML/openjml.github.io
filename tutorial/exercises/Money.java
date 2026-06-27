public class Money {
    private /*@ spec_public @*/ int dollars, cents;

    //@ requires c < 100;
    //@ ensures dollars == d && cents == c;
    public Money(int d, int c) {
        dollars = d;
        cents = c;
    }

    //@ requires this != m;
    //@ requires dollars + cents/100 <= Integer.MAX_VALUE;
    //@ requires m.dollars + m.cents/100 <= Integer.MAX_VALUE;
    /*@ ensures \result <==> (this.dollars == m.dollars
      @                        && this.cents == m.cents); @*/
    public /*@ pure @*/ boolean equals(Money m) {
        this.normalize();
        m.normalize();
        return this.dollars == m.dollars && this.cents == m.cents;
    }
        

    //@ requires dollars + cents/100 <= Integer.MAX_VALUE;
    //@ ensures cents < 100;
    public void normalize() {
        if (cents >= 100) {
            dollars += cents/100;
            cents = cents % 100;
        }
    }
}

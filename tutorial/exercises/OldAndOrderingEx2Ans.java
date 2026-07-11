// openjml --esc OldAndOrderingEx2Ans.java
public class OldAndOrderingEx2Ans {
    private /*@ spec_public @*/ long number;
    private /*@ spec_public @*/ int aDivisor;

    //@ requires div > 0;
    //@ requires n >= 0;
    //@ requires n % div == 0;
    //@ ensures number == n && aDivisor == div;
    //@ ensures n % div == 0;
    public OldAndOrderingEx2Ans(long n, int div) {
        number = n;
        aDivisor = div;
    }
}
    
        

// openjml --esc ArithmeticExample2Ans.java
public class ArithmeticExample2Ans {
    //@ spec_public
    private int playerHealth;
	
    public int updatePlayerHealth(int dmg) {
	//@ assume 0 <= dmg < Integer.MAX_VALUE;
	//@ assume 0 < playerHealth;
        playerHealth -= dmg;
        if (playerHealth < 0) {
            playerHealth = 0;
        }
        return playerHealth;
    }
}

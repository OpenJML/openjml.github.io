// openjml --esc ArithmeticExample2.java
public class ArithmeticExample2 {
    private int playerHealth;
	
    public int updatePlayerHealth(int dmg) {
        playerHealth -= dmg;
        if (playerHealth < 0) {
            playerHealth = 0;
        }
        return playerHealth;
    }
}

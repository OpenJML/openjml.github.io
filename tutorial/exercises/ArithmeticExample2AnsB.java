// openjml --esc ArithmeticExample2AnsB.java
public class ArithmeticExample2AnsB {
    private int playerHealth;
	
    public int updatePlayerHealth(int dmg) {
        if (dmg < 0 || playerHealth <= 0) {
            return playerHealth;
        }
        // here 0 <= dmg && 0 < playerHealth;
        playerHealth -= dmg;
        if (playerHealth < 0) {
            playerHealth = 0;
        }
        return playerHealth;
    }
}

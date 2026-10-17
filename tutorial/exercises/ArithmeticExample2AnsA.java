// openjml --esc ArithmeticExample2AnsA.java
public class ArithmeticExample2AnsA {
    private int playerHealth;
	
    public int updatePlayerHealth(int dmg) {
        //@ assume 0 <= dmg;
	//@ assume 0 < playerHealth;   
        playerHealth -= dmg;
        if (playerHealth < 0) {
            playerHealth = 0;
        }
        return playerHealth;
    }
}

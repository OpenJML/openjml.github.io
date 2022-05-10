public class ArithmeticExample2 {
	//@ spec_public
	private int playerHealth;
	
	//@ requires 0 <= dmg < Integer.MAX_VALUE;
	//@ requires 0 < playerHealth;
	public int updatePlayerHealth(int dmg) {
		if(playerHealth > dmg) {
			return (playerHealth + dmg);
		}else {
			return 0;
		}
	}
}
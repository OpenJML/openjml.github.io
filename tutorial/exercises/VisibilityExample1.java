public class VisibilityExample1 {

	//@ spec_public
	private static int MAXHEALTH = 100;
	//@ spec_public
	private int playerHealth = 100;
	
	//@ requires 0 <= dmg < Integer.MAX_VALUE;
	//@ requires 0 < playerHealth;
	//@ assigns playerHealth;
	public void damage(int dmg) {
		if (playerHealth > dmg) {
			playerHealth -= dmg;
		} else {
			playerHealth = 0;
		}
	}

	//@ requires 0 <= hp < Integer.MAX_VALUE;
	//@ requires 0 < playerHealth;
	//@ requires playerHealth + hp < MAXHEALTH;
	//@ assigns playerHealth;
	//@ ensures playerHealth <= MAXHEALTH;
	public void heal(int hp) {
		if (MAXHEALTH >= (playerHealth + hp)) {
			playerHealth += hp;
		}
	}

}

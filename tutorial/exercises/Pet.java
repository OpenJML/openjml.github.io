public class Pet {
	
	public String species;
	public String name;
	public int yearsOld;
	public double weight;
	public boolean vaccinated;
	/**total number of pet's owned by the owner**/
	//@ spec_public
	private static int numPets = 0; 
	
	//@ public normal_behavior
	//@		requires species.length() > 0;
	//@ 	requires name.length() > 0;;
	//@ 	requires 0 <= yearsOld < 100;
	//@ 	requires !Double.isNaN(weight);
	//@ 	requires weight > 0;
	//@ 	assigns numPets;
	//@		ensures this.species == species;
	//@ 	ensures this.name == name;
	//@ 	ensures this.yearsOld == yearsOld;
	//@ 	ensures this.weight == weight;
	//@ 	ensures this.vaccinated == vaccinated;
	//@ 	ensures numPets == \old(numPets) + 1;
	public Pet(String species, String name, int yearsOld, double weight, boolean vaccinated) {
		this.species = species;
		this.name = name;
		this.yearsOld = yearsOld;
		this.weight = weight;
		this.vaccinated = vaccinated;
		
		//@ assume numPets + 1 < Integer.MAX_VALUE;
		numPets++;
	}
}
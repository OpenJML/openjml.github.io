---
title: JML Tutorial - Exercises - Method Specifications
---
# Method Specifications Exercises:
## **Question 1**
**Given the program below, correct the order of the specifications for easier readability.**
```Java
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
  	//@ 	ensures numPets == \old(numPets) + 1;
  	//@ 	assigns numPets;
  	//@	ensures this.species == species;
	//@	requires species.length() > 0;
  	//@ 	ensures this.name == name;
	//@ 	requires name.length() > 0;
  	//@ 	ensures this.yearsOld == yearsOld;
	//@ 	ensures this.weight == weight;
	//@ 	requires 0 <= yearsOld < 100;
  	//@ 	requires weight > 0;
	//@ 	requires !Double.isNaN(weight);
	//@ 	ensures this.vaccinated == vaccinated;
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
```

**Learning Objectives:**
+ Understand the standard for writing specifications in JML
+ Understand the importance of ordering specifications
+ Understand that the order of preconditions do matter

## **[Answer Key](MethodSpecificationsExKey.md)**

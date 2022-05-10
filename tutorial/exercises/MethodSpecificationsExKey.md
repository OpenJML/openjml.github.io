---
title: JML Tutorial - Exercises - Method Specifications
---
# Method Specifications Exercises Key:
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
  	//@	ensures numPets == \old(numPets) + 1;
  	//@	assigns numPets;
  	//@	ensures this.species == species;
	//@	requires species.length() > 0;
  	//@	ensures this.name == name;
	//@	requires name.length() > 0;
  	//@	ensures this.yearsOld == yearsOld;
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
**Asnwer and Explanation:**
The function above will verify with no issue, however if we take a closer look at our specifications of our constructor we see that everything is out of order - making it difficult to read. While OpenJML does not have any specific order syntax of specifications, some of specifications logically don’t make sense and could cause an error. The class `Pet` is taking in the `species`, `name`, `age`, `weight`, and the vaccination status, `vaccinated`, of the pet to be created. There is also a static integer variable `numPets` which will increment every time a new pet object is created.
 
We know that for constructors we need to include the header `normal_behavior` which is included already. However, the first specification to follow is a postcondition statement that is saying what `numPets` should be after the constructor is called. While OpenJML will not fail to verify, this logically doesn't make sense as it isn't until after this postcondition that we say that the constructor is assigning `numPets`. Following this we see that all the ensures statements come before our requires statements which doesn't logically make sense. We should keep to the standard of preconditions, frame conditions, postconditions, and termination statements. So we can rewrite the specifications in the following order:
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
	//@	requires species.length() > 0;
	//@ 	requires name.length() > 0;;
	//@ 	requires 0 <= yearsOld < 100;
	//@ 	requires !Double.isNaN(weight);
	//@ 	requires weight > 0;
	//@ 	assigns numPets;
	//@	ensures this.species == species;
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
```
However, it is important to note that the order of preconditions DO matter. For example the precondition stating that `weight` cannot be NaN needs to come before checking that `weight` is greater than zero - it wouldn’t make sense to check that `weight > 0` if `weight` is NaN.    

**Learning Objective:** 
The goal of this exercise is to simply check that the student understands that while OpenJML won't fail to verify a program with specifications all over the place, it is important to follow the standard for readability. Additionally, the student does need to pay attention to the order of their preconditions, as order does matter for preconditions.

## **Resources:**
+ [Method Specifications Exercises](MethodSpecificationsEx.md)
+ [Question 1 Java](Pet.java)

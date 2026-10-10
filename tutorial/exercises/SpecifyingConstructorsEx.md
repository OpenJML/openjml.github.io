---
title: JML Tutorial - Exercises - Specifying Constructors 
---
# Specifying Constructors Exercises:
## [Specifying Constructors Tutorial](https://www.openjml.org/tutorial/Constructors)

## **Question 1**
**(a) Determine the specifications needed to verify the program below.**
**(b) Explain why the program can assert s1.id < s2.id in the createStudents() function.**
```Java
{% include_relative Student.java %}
```
**Note:** The `spec_public` attribute is not important for this exercise, and only serves to avoid a visibility error. See the [Visibility section](https://www.openjml.org/tutorial/Visibility.html) of this tutorial for details.

**Learning Objectives:**
+ Understand how to use constructor specification syntax
+ Understand `normal_behavior`
+ Understand `pure` and not `pure` constructors 
+ Gain more experience writing preconditions and postconditions 
+ Gain more experience with the `assert` clause

## **Question 2**
**Determine the strongest specifications needed to verify the program.**
```Java
public class Book {

	//@ spec_public
	private String title;
	//@ spec_public
	private int pages;
	//@ spec_public
	private String author;
	//@ spec_public
	private String publication; //mm-dd-yy
	//@ spec_public
	private static int TBABooks = 0; 

	public Book(String title, int pages, String author, String publication) {
		this.title = title;
		this.pages = pages;
		this.author = author;
		this.publication = publication;		
	}
	
	public Book(String publication) {
		//@ assume 0 < TBABooks+1 < Integer.MAX_VALUE;
		TBABooks++;
		this.title = "TBA";
		this.pages = 0;
		this.author = "TBA";
		this.publication = publication;
	}

	public void createBooks() {
		Book b1 = new Book("TBA"); 
		Book b2 = new Book("1984", 328, "George Orwell", "06-08-49");
		Book b3 = new Book("The Great Gatsby", 208, "F. Scott Fitzgerald", "04-10-25");
		Book b4 = new Book("TBA");				
	}
}
```
**Learning Objectives:**
+ Gain more experience with `pure` and not `pure` constructors
+ Gain more experience writing the specifications for constructors 

## **[Answer Key](SpecifyingConstructorsExKey.md)**


## Resources
+ [Question 1 Java](Student.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)

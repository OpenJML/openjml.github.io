---
title: JML Tutorial - Exercises - Specifying Constructors 
---
# Specifying Constructors Exercises:
## **Question 1**
**(a) Determine the specifications needed to verify the program below.**
**(b) Explain why the program can assert s1.id < s2.id in the createStudents() function.**
```Java
public class Student {
	
	//@ spec_public
	private String firstName;
	//@ spec_public
	private String lastName;
	//@ spec_public
	private int grade;
	//@ spec_public
	private double GPA;
	//@ spec_public
	private long id;
	//@ spec_public
	private static long count = 0;

	public Student(String firstName, String lastName, int grade, double GPA) { 
		//@ assume count+1 < Integer.MAX_VALUE;
		count ++;
		
		this.firstName = firstName;
		this.lastName = lastName;
		this.grade = grade;
		this.GPA = GPA;
		this.id = count;
		
	}
	
	//@ requires count < Integer.MAX_VALUE-1;
	public void createStudents() {
		Student s1 = new Student("John", "Doe", 12, 3.7);
		Student s2 = new Student("Jane", "Doe", 11, 2.5);
		//@ assert s1.id < s2.id;
	}
}
```
**Note:** `spec_public` will be discussed in the [“Visibility”](https://www.openjml.org/tutorial/Visibility) tutorial, but for now just understand that `spec_public` is used when we have private variables that we want to use in our JML specifications so that we don’t have any visibility errors.

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


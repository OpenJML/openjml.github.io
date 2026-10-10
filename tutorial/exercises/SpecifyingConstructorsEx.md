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

A hint about question 1(b) may be in order: think about the default frame conition for the constructor of the class `Student` and how the constructor call might affect the state of the object `s1`; is there a specification that could limit the effects of that constructor call?

**Learning Objectives:**
+ Understand how to use constructor specification syntax
+ Understand `normal_behavior`
+ Understand frame conditions for constructors, especially what `pure` means for a constructor

## **Question 2**
**What specifications will allow the class definition below to verify?**
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

	//@ public normal_behavior
	//@   requires title != "";
	//@   requires 0 < pages < Integer.MAX_VALUE;
	//@   requires author != "";
	//@   requires publication != "";
	//@   ensures this.title == title;
	//@   ensures this.pages == pages;
	//@   ensures this.author == author;
	//@   ensures this.publication == publication;
	public Book(String title, int pages, String author, String publication) {
		this.title = title;
		this.pages = pages;
		this.author = author;
		this.publication = publication;		
	}
	
	//@ public normal_behavior
	//@   requires publication == "TBA";
	//@   assigns TBABooks;
	//@   ensures this.title == title;
	//@   ensures this.pages == pages;
	//@   ensures this.author == author;
	//@   ensures this.publication == publication;
	//@   ensures TBABooks == \old(TBABooks) + 1;
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
            String b1title = b1.title;
            Book b2 = new Book("1984", 328, "George Orwell", "06-08-49");
            //@ assert String.equals(b1.title, b1title);
	    Book b3 = new Book("The Great Gatsby", 208, "F. Scott Fitzgerald", "04-10-25");
            Book b4 = new Book("TBA");				
	}
}
```

Hint: think about the frame condition for the constructor call.

**Learning Objectives:**
+ Understand frame conditions for constructor calls.
+ Gain more experience writing specifications for constructors.

## **[Answer Key](SpecifyingConstructorsExKey.md)**


## Resources
+ [Question 1 Java](Student.java)
+ [All exercises](https://www.openjml.org/tutorial/exercises/exercises)

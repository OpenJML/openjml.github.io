---
title: JML Tutorial - Exercises - Specifying Constructors 
---
# Specifying Constructors Exercises Key:
## **Question 1**
**(a) Determine the specifications needed to verify the program below.**
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

**Asnwer and Explanation:**
Recall what you have read in the tutorial "Specifying Constructors," when dealing with constructors we need to use the following syntax: `public normal_behavior`. `normal_behavior` essentially says that the constructor runs without throwing exceptions. Similar to method specifications, the `pure` modifier can only be used if the method default `assigns \nothing`. However, in this case we see that the constructor `Student()` is incrementing the global static variable `count` by one each time a new Student object is made. This `count` variable is then used as the id of the Student object being created.
 
Additionally, we know that when specifying constructors (like all other methods) we still need to include any preconditions and postconditions to verify the method. We might want to specify that the first and last name cannot be empty Strings, that the grade is in the range of 1-12 (first through senior), and that GPA is between 0.0 and 4.0 - also that we ensure that is not NaN. Also, since we’re incrementing `count` by one in our constructor we need to take care of potential overflow errors, so we should also include that `count < Integer.MAX_VALUE`. 

If all of these preconditions are met we can ensure that `this.variable = variable`, except for `id` which should be `this.id == count`. Note, however, that since we are dealing with Strings we could also write our postconditions in the format of `variable.equals(this.variable)`. Additionally, we can ensure that the `count` will always be equal to it's pre-state value plus one. So let's add all this together and write the following to verify the function.
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

	//@ public normal_behavior
	//@ 	requires firstName != "";
	//@		requires lastName != "";
	//@ 	requires 1 <= grade <= 12;
	//@ 	requires 0 <= GPA <= 4.0 && !Double.isNaN(GPA);
	//@ 	requires count < Integer.MAX_VALUE;
	//@ 	assigns count;
	//@ 	ensures this.firstName == firstName;
	//@		ensures this.lastName == lastName;
	//@ 	ensures this.grade == grade;
	//@ 	ensures this.GPA == GPA;
	//@ 	ensures this.id == count;
	//@ 	ensures count == \old(count) + 1;
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
**(b) Explain why the program can assert s1.id < s2.id in the createStudents() function.**

**Asnwer and Explanation:**
The function `createStudents()` can assert `s1.id < s2.id` since when it creates `s1` and `s2` it calls the constructor `Student()` - which is not `pure`. `Student()` is not `pure` because it assigns a value to `count` which is not a non-static field of Student. This `count` variable is then set as the value of the student's `id`. So when `s1` is created, `count` = `count` + 1 = (0) + 1 = 1 , so `s1.id = 1`. When `s2` is created `count` + 1 = 1 + 1 = 2, so `s2.id = 2`. Therefore, we can `assert` that `s1.id` will be less than `s2.id` for this reason. Note, however, that this assertion can only be made if we include that `Student()` assigns `count` and that `this.id == count`, and `count = \old(count) + 1`, otherwise, this assertion would fail to verify. 

**Learning Objective:** 
The goal of this exercise is to see if the student understands how to use constructor specification syntax. We want the student to understand how it's very similar to what they have been doing up until this point, but there are just a few differences (i.e. normal_behavior). Additionally, the exercise addresses the difference between `pure` and non-pure functions, and shows the student that when we are modifying something other than the non-static fields - the function is not `pure`. Furthermore, part (b) checks to see if the student understands how assertions are still heavily dependent on other specifications. If we don't include all the specifications needed surrounding the `count` variable, the assert in the `createStudents()` function cannot be verified. The exercise is verbose in that checks that the student understands past tutorials and combines a lot of different topics the student should be familiar with now.

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
**Asnwer and Explanation:**
Let's take a look at the program above. The class `Book` has four non-static fields: `title`, `pages`, `author`, and `publication`. There is also a static int variable `TBABooks` which is initialized to zero. The first constructor of Book takes in four variables which the non-static fields will be set to. The second constructor of Book takes in only one variable `String publication`; within `Book(String publication)` the static int `TBABooks` is incremented by one, and the remaining non-static fields are initialized. Finally, the `createBooks()` function simply calls the constructors and creates some objects of Book.
 
Let's determine the specifications for `Book(String title, int pages, String author, String publication)`. Firstly, since we're dealing with a constructor we know that we need to include the header `public normal_behavior`. Now let's determine any preconditions we might need; we want to make sure our String variables aren't empty, that `pages` is between zero and Integer.MAX_VALUE (to avoid overflow). Given these preconditions we can ensure that `this.variable = variable`. Additionally, since this first Book constructor is not modifying any memory locations we can say that it is `pure`. So we can write the following:
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
	//@ 	requires title != "";
	//@ 	requires 0 < pages < Integer.MAX_VALUE;
	//@ 	requires author != "";
	//@ 	requires publication != "";
	//@ 	ensures this.title == title;
	//@ 	ensures this.pages == pages;
	//@ 	ensures this.author == author;
	//@ 	ensures this.publication == publication;
	//@ pure
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
Now, let's tackle the second Book constructor. Same as always we can include `public normal_behavior` and start including any preconditions we might need. We want to require that if this Book constructor is being called, then `publication == "TBA"`. Essentially, this constructor is creating a Book object for a book that is not yet released so we require that the publication be TBA (to be announced). Additionally, the constructor still set's the fields of Book, but it is not setting it to any values passed in so we can ensure that this.variable will equal the same thing every time. However, notice that within this constructor `TBABooks` is being incremented so we have to specify this by saying `assigns TBABooks` since this memory location is being modified. As such we know this constructor is not `pure`, so we can write the following:
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
	//@ 	requires title != "";
	//@ 	requires 0 < pages < Integer.MAX_VALUE;
	//@ 	requires author != "";
	//@ 	requires publication != "";
	//@ 	ensures this.title == title;
	//@ 	ensures this.pages == pages;
	//@ 	ensures this.author == author;
	//@ 	ensures this.publication == publication;
	//@ pure
	public Book(String title, int pages, String author, String publication) {
		this.title = title;
		this.pages = pages;
		this.author = author;
		this.publication = publication;		
	}
	
	//@ public normal_behavior
	//@ 	requires publication == "TBA";
	//@ 	assigns TBABooks;
	//@ 	ensures this.title == title;
	//@ 	ensures this.pages == pages;
	//@ 	ensures this.author == author;
	//@ 	ensures this.publication == publication;
	//@ 	ensures TBABooks == \old(TBABooks) + 1;
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
**Learning Objective:**
The goal of this exercise is to show the student more exercises that uses the `pure` modifier in practice. In the program we have two constructors that might initially seem very similar, but once we break it down we see all the subtle differences and how their specifications need to reflect their uniqueness. The student should be able to recognize that the first constructor is `pure` and the second is not due to it incrementing `TBABooks`.

## **Resources:**
+ [Specifying Constructors Exercises](SpecifyingConstructorsEx.md)
+ [Question 1 Java](Student.java)
+ [Question 2 Java](Book.java)

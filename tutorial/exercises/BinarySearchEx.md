**Specify and correctly implement a method that takes a sorted integer array, and an element and uses a binary search to check whether the element occurs in the array (and returns _true_ when it occurs in the array and _false_ otherwise).**

The task is to specify and implement a binary search method that takes a sorted integer array, and an element and uses a binary search to check whether the element occurs in the array (and returns _true_ when it occurs in the array and _false_ otherwise).

First, what do we know needs to be true for a binary search function? We know that the array passed in must already be sorted, it cannot be empty, and depending what we choose as our parameters, we need to make sure that everything is within the range of zero to the array's length. Let's say that we decide to code the following binary search function:
```Java
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```
In the code above we take in four parameters: the array `a`, the `low` index, the `high` index, and `key` - which is what we are looking for. Within the function we create our variable `mid`, followed by a while-loop that runs while `low <= high` - typical of any binary search. Within the while loop we find our `mid` index and assess if the `key` is greater than `a[mid]`, less than `a[mid]`, or `a[mid]`. Finally, we `return -1` if we find that the key is not in the array. 

Now that we understand what is going on, let's start adding our JML specifications. First we need to make sure that the array != null, secondly that `low` and `high` are within the range of `a`, and finally that the array is sorted. We can come up with the first requirements pretty easily, as seen below:
```Java
//@ requires a != null;
//@ requires 0 <= low < a.length;
//@ requires 0 <= high < a.length;
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```
Note that in JML objects (including arrays) must not be null, so writing `a != null` is redundant and can be omitted.

However, now we need to make sure that the array `a` is sorted. How do we do this? We need to use the `\forall` clause, which will be discussed in the "[JML Expressions](https://www.openjml.org/tutorial/Expressions)" tutorial. So for now don't worry about the syntax, let's just make sure we understand what the requirement is doing.
```Java
//@ requires a != null;
//@ requires 0 <= low < a.length;
//@ requires 0 <= high < a.length;
//@ requires (\forall int i; 0 < i && i < a.length; a[i-1] <= a[i]);
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```
The last requirement is simply checking that that the array is sorted. The `\forall` clause acts as a for-loop in JML, and can be very useful when we want to ensure that something is true for a range of values. In this case the `\forall` clause is checking that the array is sorted for `i` greater than zero and less than `a.length`. We also need to include some assume statements within the while-loop to make sure that `a[mid]` is not out of bounds of the array. We will study the assume clause in more depth in the "[Assume Statements](https://www.openjml.org/tutorial/AssumeStatement)" tutorial. For now, just know that the code above will cause error unless the assume statement is included as seen below:
```Java
//@ requires a != null;
//@ requires 0 <= low < a.length;
//@ requires 0 <= high < a.length;
//@ requires (\forall int i; 0 < i && i < a.length; a[i-1] <= a[i]);
public int binarySearch(int[] a, int low, int high, int key) {
	int mid;		
	
	while(low <= high) {
		//@ assume 0 <= (low+high) < a.length;
		mid = (low+high)/2;
		if(a[mid] == key)
			return mid;
		if(a[mid] > key)
			high = mid - 1;
		if(a[mid] < key)
			low = mid + 1;
	}
	return -1;
}
```

**Learning Objective:**

The goal of this exercise is to test if the user understands how requirements might be used with arrays since there are some very important preconditions we have to consider. Depending how the student chooses to write their binary search will determine what their requirements look like; however, they should understand that while the syntax of the precondition statements might alter from program to program it is still vital that the preconditions are included. For example, if the student were to only pass in the array and the key, they should still include a precondition that ensures that the length of the array is not outside the range of the type int. Students should also know to check that the array is not empty regardless of how they code their binary search. It also introduces some new concepts like the `\forall` clause which we do not expect the student to understand fully - but we want them to understand how requirements can be used to ensure that the function they wrote performs properly. In this case the student should be able to recognize that a binary search *requires* that the array we are searching through is already sorted. This allows the students to know without a doubt that the program will throw an exception if this is not met and will allow them to spend less time sifting through results that don't make sense.

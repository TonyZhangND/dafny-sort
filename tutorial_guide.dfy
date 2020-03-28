method Max(a: int, b:int) returns (c: int) 
ensures (c == a && c >= b) || (c == b && c >= a)
{
    if a > b {
        c := a;
    } else {
        c := b;
    }
}

method Testing() { 
    var v := Max(10, 20);
    assert v == 20;
}

/* Ex 2: Using a precondition, change Abs to say it can only be called on negative values. 
Simplify the body of Abs into just one return statement and make sure the method 
still verifies. */
method Abs(x: int) returns (y: int) 
    requires x == -1
    ensures y == -x
{ 
    y := x + 2;
 }

 /* Exercise 3. Keeping the postconditions of Abs the same as above, change the body of Abs
  to just y := x + 2. What precondition do you need to annotate the method with in order 
  for the verification to go through? What precondition doe you need if the body is 
  y := x + 1? What does that precondition say about when you can call the method? */


/* Exercise 4. Write a function max that returns the larger of two given integer 
parameters. Write a test method using an assert that checks that your function 
is correct. */
function method max(a: int, b: int): int { 
    if a > b then a else b
 }

 /* Exercise 5. Change your test method from Exercise 4 to capture the value of max to a 
 variable, and then do the checks from Exercise 4 using the variable. Dafny will reject 
 this program because you are calling max from real code. Fix this problem using a 
 function method. */

 method Testing1() { 
    assert max(10, 20) == 20;
}

function fib(n: nat): nat
{
   if n == 0 then 0 else
   if n == 1 then 1 else
                  fib(n - 1) + fib(n - 2)
}

/* Exercise 9. The ComputeFib method above is more complicated than necessary. 
Write a simpler program by not introducing a as the Fibonacci number that precedes b, but 
instead introducing a variable c that succeeds b. Verify your program is correct according
to the mathematical definition of Fibonacci. */
method ComputeFib9(n: nat) returns (b: nat)
   ensures b == fib(n)
{
   if n == 0 { return 0; }
   var i: int := 1;
   var c := 1;
       b := 1;
   while i < n
      invariant 0 < i <= n
      invariant c == fib(i + 1)
      invariant b == fib(i)
   {
      c, b := b + c, c;
      i := i + 1;
   }
}

/* Exercise 10. Starting with the completed ComputeFib method above, delete the if 
statement and initialize i to 0, a to 1, and b to 0. Verify this new program by adjusting
the loop invariants to match the new behavior. */
method ComputeFib10(n: nat) returns (b: nat)
    ensures b == fib(n)
{
    var i: int := 0;
    var a := 1;
       b := 0;
    while i < n
        decreases n - i
        invariant 0 <= i <= n
        invariant b == fib(i)
        invariant a == fib(i + 1)
    {
        a, b := a + b, a;
        i := i + 1;
    }
}

/* Exercise 11. In the loop above, the invariant i <= n and the negation of the loop guard
allow us to conclude i == n after the loop (as we checked previously with an assert. Note 
that if the loop guard were instead written as i != n (as in Exercise 8), then the 
negation of the guard immediately gives i == n after the loop, regardless of the loop 
invariant. Change the loop guard to i != n and delete the invariant annotation. 
Does the program verify? What happened? */
method ex11() {
    var i := 0;
    var n := 10;
    while i != n
        invariant n - i >= 0
        decreases n - i
    {
        i := i + 1;
    }
}

method Find(a: array<int>, key: int) returns (index: int)
   ensures 0 <= index ==> index < a.Length && a[index] == key
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != key
{
   index := 0;
   while index < a.Length
      invariant 0 <= index <= a.Length
      invariant forall k :: 0 <= k < index ==> a[k] != key
   {
      if a[index] == key { return; }
      index := index + 1;
   }
   index := -1;
}

/* Exercise 12. Write a method that takes an integer array, which it requires to have at 
least one element, and returns an index to the maximum of the array's elements. 
Annotate the method with pre- and postconditions that state the intent of the method, and 
annotate its body with loop invariant to verify it. */

method FindMax(a: array<int>) returns (i: int) 
    requires a.Length >= 1
    ensures 0 <= i < a.Length
    ensures forall k :: 0 <= k < a.Length ==> a[i] >= a[k]
{
    var max := a[0];
    i := 0;
    var k := 1;
    while k < a.Length 
        invariant 0 <= i < a.Length
        invariant 0 <= k <= a.Length
        invariant max == a[i]
        invariant forall j :: 0 <= j < k ==> max >= a[j]
        decreases a.Length - k
        {
        if a[k] > max {
            i := k;
            max := a[k];
        }
        k := k + 1;
    }
}

/* Exercise 13. Modify the definition of the sorted predicate so that it returns true 
exactly when the array is sorted and all its elements are distinct. */
predicate sorted(a: array<int>)
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k] && (j != k ==> a[k] != a[j])
}

method BinarySearch(a: array<int>, value: int) returns (index: int)
   requires 0 <= a.Length && sorted(a)
   ensures 0 <= index ==> index < a.Length && a[index] == value
   ensures index < 0 ==> forall k :: 0 <= k < a.Length ==> a[k] != value
{
   var low, high := 0, a.Length;
   while low < high 
      invariant 0 <= low <= high <= a.Length
      invariant forall i ::
         0 <= i < a.Length && !(low <= i < high) ==> a[i] != value
   {
      var mid := (low + high) / 2;
      if a[mid] < value
      {
         low := mid + 1;
      }
      else if value < a[mid]
      {
         high := mid;
      }
      else
      {
         return mid;
      }
   }
   return -1;
}



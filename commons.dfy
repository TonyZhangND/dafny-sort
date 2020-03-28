module Commons {

/* Returns True iff a is sorted */
predicate sorted(a: array<int>)
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

method Copy(a: array<int>) returns (b: array<int>) 
    ensures multiset(a[..]) ==  multiset(b[..])
    ensures a.Length == b.Length
{ 
    b := new int[a.Length];
    var i := 0;
    while i < a.Length 
        decreases a.Length - i
        invariant a.Length == b.Length
        invariant 0 <= i <= a.Length
        invariant forall k :: 0 <= k < i ==> a[k] == b[k]
    {
        b[i] := a[i];
        i := i + 1;
    }
    assert a[..] == b[..];
}

method Swap(a: array<int>, i: int, j: int) 
    modifies a
    requires 0 <= i < a.Length
    requires 0 <= j < a.Length
    // Nothing else is changed besides a[i] and a[j]
    ensures forall x :: 0 <= x < a.Length && x != i && x!= j ==> a[x] == old(a[x])
    // a[i] and a[j] are swapped
    ensures a[j] == old(a[i]) && a[i] == old(a[j])
{
    var ai, aj := a[i], a[j];
    a[i] := aj;
    a[j] := ai;
}
}
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

method SelectionSort(a: array<int>)
    modifies a
    ensures multiset(a[..]) ==  multiset(old(a)[..])
    ensures sorted(a)
{ 
    var k := 0;

    while k != a.Length 
        decreases a.Length - k
        invariant 0 <= k <= a.Length
        invariant multiset(a[..]) ==  multiset(old(a)[..])
        // a[..k] is sorted
        invariant forall r, s :: 0 <= r < s < k ==> a[r] <= a[s]
        // everything in a[k..] is greater than everything in a[..k]
        invariant forall s :: k <= s < a.Length ==> (forall r :: 0 <= r < k ==> a[r] <= a[s])
    {
        var l := k;
        while l != a.Length 
            decreases a.Length - l
            invariant k <= l <= a.Length
            // a[..k] is sorted
            invariant forall r, s :: 0 <= r < s <= k ==> a[r] <= a[s]
            // everything in a[k..] is greater than everything in a[..k]
            invariant forall s :: k <= s < a.Length ==> (forall r :: 0 <= r < k ==> a[r] <= a[s])
            // a[k] is smaller than everything in a[k..l]
            invariant forall r :: k <= r < l  ==> a[k] <= a[r]
        {
            if a[l] < a[k] {
                Swap(a, k, l);
            }
            l := l + 1;
        }
        k := k + 1;
    }
}
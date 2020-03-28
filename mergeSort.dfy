predicate sorted(a: array<int>)
   reads a
{
   forall j, k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
}

 
method Split(a: array<int>) returns (left: array<int>, right: array<int>) 
    requires a.Length >= 2
    ensures a.Length == left.Length + right.Length
    ensures left.Length < a.Length && right.Length < a.Length
    ensures a[..] ==  left[..] + right[..]
{
    if a.Length % 2 == 0 {
        left := new int[a.Length/2];
        right := new int[a.Length/2];
    } else {
        left := new int[a.Length/2];
        right := new int[a.Length/2 + 1];
    }

    var i := 0;
    while i < left.Length
        decreases left.Length - i
        invariant 0 <= i <= left.Length
        invariant left[..i] == a[..i]
    {
        left[i] := a[i];
        i := i + 1;
    }

    while i - left.Length < right.Length 
        decreases right.Length - (i - left.Length)
        invariant 0 <= i <= a.Length
        invariant left[..] == a[..left.Length]
        invariant right[..(i - left.Length)] == a[left.Length..i]
    {
        right[i-left.Length] := a[i];
        i := i + 1;
    }

    assert left[..] == a[..left.Length];
    assert right[..] == a[left.Length..];
}


method MergeSort(a: array<int>) returns (c: array<int>)
    decreases a.Length - 1
    ensures multiset(a[..]) ==  multiset(old(a)[..])
    ensures sorted(c)
    ensures c.Length == a.Length
{ 
    if a.Length > 1 {
        var left, right := Split(a); 
        assert left.Length >= 1 && right.Length >= 1;
        var left_res := MergeSort(left);
        var right_res := MergeSort(right);
        c := Merge(left_res, right_res);
    } else {
        c := a;
    }
}


method Merge(a: array<int>, b: array<int>) returns (c: array<int>)
    requires sorted(a) && sorted(b)
    requires a.Length >= 1 && b.Length >= 1
    ensures c.Length == a.Length + b.Length
    ensures multiset(c[..]) ==  multiset(a[..]) + multiset(b[..])
    ensures sorted(c)
{ 
    c := new int[a.Length + b.Length];

    // Step 1. Populate c up to min(a.Length, b.Length)
    var i := 0;
    var a_head, b_head := 0, 0;
    while a_head < a.Length && b_head < b.Length 
        decreases c.Length - a_head - b_head
        invariant sorted(a) && sorted(b)
        invariant 0 <= i < c.Length
        invariant 0 <= a_head <= a.Length
        invariant 0 <= b_head <= b.Length
        invariant i == a_head + b_head

        // a[a_head] and b[b_head] is greater than everything in c[..i]
        invariant forall r :: 0 <= r < i ==> ( a_head < a.Length ==> c[r] <= a[a_head]);
        // b[b_head] is greater than everything in c[..i]
        invariant forall r :: 0 <= r < i ==> (b_head < b.Length ==> c[r] <= b[b_head]);
        // c[..i] contains everything in a[..a_head] and b[..b_head]
        invariant multiset(c[..i]) ==  multiset(a[..a_head]) + multiset(b[..b_head])
        // c[..i] is sorted
        invariant forall j, k :: 0 <= j < k < i ==> c[j] <= c[k]
    {
        if a[a_head] < b[b_head] {
            c[i] := a[a_head];
            a_head := a_head + 1;
        } else {
            c[i] := b[b_head];
            b_head := b_head + 1;
        }
        i := i + 1;
        assert multiset(c[..i]) ==  multiset(a[..a_head]) + multiset(b[..b_head]);
    }

    // Step 2. Append a[a_head..a.Length] and b[b_head..b.Length], at least one of which
    // is empty, into c.

    while a_head < a.Length 
        decreases a.Length - a_head
        invariant sorted(a) && sorted(b)
        invariant a_head <= a.Length
        invariant i == a_head + b_head
        invariant a.Length - a_head > 0 ==>  a.Length - a_head == c.Length - i
        invariant multiset(c[..i]) == multiset(a[..a_head]) + multiset(b[..b_head])
        // a[a_head] is greater than everything in c[..i]
        invariant forall r :: 0 <= r < i && a_head < a.Length ==> a[a_head] >= c[r]
        // b[b_head] is greater than everything in c[..i]
        invariant forall r :: 0 <= r < i ==> (b_head < b.Length ==> b[b_head] >= c[r])
        // c[..i] is sorted
        invariant forall j, k :: 0 <= j < k < i ==> c[j] <= c[k]
    {
        c[i] := a[a_head];
        a_head := a_head + 1;
        i := i + 1;
    }
    assert a[..a.Length] == a[..] && b[..b.Length] == b[..];

    while b_head < b.Length 
        decreases b.Length - b_head
        invariant sorted(a) && sorted(b)
        invariant 0 <= a_head == a.Length
        invariant 0 <= b_head <= b.Length
        invariant i == a_head + b_head
        invariant b.Length - b_head > 0 ==> b.Length - b_head == c.Length - i
        invariant multiset(c[..i]) == multiset(a[..]) + multiset(b[..b_head]);
        // b[b_head] is greater than everything in c[..i]
        invariant forall r :: 0 <= r < i ==> (b_head < b.Length ==> b[b_head] >= c[r])
        // c[..i] is sorted
        invariant forall j, k :: 0 <= j < k < i ==> c[j] <= c[k]
    {
        assert multiset(c[..i]) == multiset(a[..]) + multiset(b[..b_head]);
        c[i] := b[b_head];
        assert multiset(c[..i+1]) == multiset(a[..]) + multiset(b[..b_head+1]);
        b_head := b_head + 1;
        i := i + 1;
    }
    assert b_head == b.Length;
    assert c[..c.Length] == c[..];
    assert multiset(c[..]) ==  multiset(a[..]) + multiset(b[..]);
}

method Main()
{
    print "Running MergeSort\n";
    var a := new int[3];
    a[0], a[1], a[2] := 8, 6, 4;
    print "the sorted version of ";
    print a;
    print " is ";
    var a_sorted := MergeSort(a);
    print a_sorted;
    print "\n";
}
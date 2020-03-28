include "commons.dfy"

module SelSort{

import opened Commons

method selectionSort(a: array<int>)
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
}
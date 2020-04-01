include "mergeSort.dfy"
include "selSort.dfy"

module Sort {
  import opened MergeSort
  import opened SelSort

method Main()
{
    print "Running MergeSort\n";
    var a := new int[3];
    a[0], a[1], a[2] := 8, 6, 4;
    print "The sorted version of ";
    print a;
    print " is ";
    var a_sorted := mergeSort(a);
    print a_sorted;
    print "\n";
    
    var b := new int[10];
    b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7], b[8], b[9] := 8, 6, 4, 2, 19, 54, 16, 5, 28, 37;
    print "The sorted version of ";
    print b;
    print " is ";
    var b_sorted := mergeSort(b);
    print b_sorted;
    print "\n";

    print "\nRunning SelectionSort\n";
    var c := new int[3];
    c[0], c[1], c[2] := 8, 6, 4;
    print "The sorted version of ";
    print c;
    print " is ";
    selectionSort(c);
    print c;
    print "\n";
    
    var d := new int[10];
    d[0], d[1], d[2], d[3], d[4], d[5], d[6], d[7], d[8], d[9] := 8, 6, 4, 2, 19, 54, 16, 5, 28, 37;
    print "The sorted version of ";
    print d;
    print " is ";
    selectionSort(d);
    print d;
    print "\n";
}
}
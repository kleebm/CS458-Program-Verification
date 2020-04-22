method abs(A: array<int>, size: nat)
modifies A
requires 0 < A.Length && size <= A.Length
//ensures forall j :: 0 <= j < size  ==> (A[j] == old(A[j]) || -A[j] == old(A[j]))  
ensures forall j :: 0 <= j < size ==> old(A[j]) >= 0 ==> A[j] >= 0
ensures forall j :: 0 <= j < size ==> old(A[j]) < 0 ==> A[j] >= 0  
//ensures forall j :: size <= j < A.Length ==> old(A[j]) == A[j] 
{
    var i := 0;
	while i < size
	decreases size - i
	invariant 0 <= i <= size
	invariant forall j :: 0<= j < i  ==> old(A[j]) >= 0 ==> A[j] >= 0 
	invariant forall j :: 0 <= j < i  ==> old(A[j]) < 0 ==> A[j] >= 0 
	{
		if (A[i] < 0) 
    	{
			A[i] := -A[i];
		}
    	i := i + 1;
	}
}

method Testing()
{
var a := new int[10];
var size := 5;
a[0],a[1],a[2],a[3],a[4] := 2,-4,6,-3,-2;
abs(a,5);
assert a[1] == 4;
}
predicate sorted(A: array<int>, i: int, j: int)
reads A
{forall k :: 0 <= i <= k < j < A.Length ==> A[k] <= A[k+1] }

predicate all_smaller(A: array<int>, a: int, b: int, c: int)
reads A
{forall i :: 0 <= a <= i <= b < A.Length && 0 <= c < A.Length ==> A[i] <= A[c]}

method MaxIndex(A: array<int>, size: nat) returns(r: nat)
requires A.Length > 0 && 0 < size <= A.Length
ensures r < A.Length && r < size
ensures forall k :: 0 <= k < size < A.Length ==> A[r] >= A[k]
//ensures all_smaller(A, 0, size, r)
{
  r := 0;
  var i := 1;
  while i < size
  decreases size - i
  invariant 1 <= i <= size && 0<= r < size
  invariant forall j :: 0 <= j < i  ==> A[r] >= A[j]
  //invariant all_smaller(A,0,r,r) || all_smaller(A,0,r,i)
  {
    if A[r] < A[i]
    {
      r := i;
    }
    i := i + 1;
  }
}

method SelectionSort(A: array<int>)
modifies A
requires A.Length > 0
ensures sorted(A, 0, A.Length)
ensures multiset(old(A[..])) == multiset(A[..])
{
  var i := A.Length;
  var m;
  while i >= 2
  decreases i - 2
  invariant A.Length >= i > 0
  //invariant i != A.Length ==> 0 <= m < A.Length
  invariant multiset(old(A[..])) == multiset(A[..])
  invariant all_smaller(A, i, A.Length, i-1)
  {
    m := MaxIndex(A,i);
    A[i-1],A[m] := A[m],A[i-1];
    i := i - 1;
  }
}

method Testing()
{
var a := new int[10];
var size := 5;
a[0],a[1],a[2],a[3],a[4] := 2,4,6,4,4;
SelectionSort(a);
assert a[2] <= a[3];
}
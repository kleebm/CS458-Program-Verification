method Duplicate(A: array<int>) returns(r: bool)
requires 0 < A.Length
//ensures multiset(old(A[..])) == multiset(A[..])
ensures r == exists a,b :: 0 <= a < A.Length && 0 <= b < A.Length && a != b && A[a] == A[b] 
{
  var i := 0;
  var j;
  while i < A.Length
  decreases A.Length - i
  invariant 0 <= i <= A.Length
  invariant forall k :: 0<= k <i ==> A[k] != A[i]
  {
    j := i + 1;
    while j < A.Length
    decreases A.Length - j
    invariant i < j <= A.Length
    //invariant forall k :: i <= k < j-1 ==> A[i] != A[k]
    {
      if A[i] == A[j]
      {
        return true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  return false;
}

method Testing()
{
var a := new int[5];
a[0],a[1],a[2],a[3],a[4] := 2,4,6,4,4;
var r := Duplicate(a);
assert 0 <= 1 < 3 < a.Length;
assert a[1] == a[3];
assert r == true;
}
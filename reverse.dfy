function reverse<A>(s:seq<A>) : seq<A>
{
  if |s| == 0 then
    []
  else
    reverse(s[1..]) + [s[0]]
}

method Swap<T>(a: array<T>, i: int, j: int)
  requires 0 <= i < a.Length;
  requires 0 <= j < a.Length;
  modifies a;
  ensures a[i] == old(a[j]);
  ensures a[j] == old(a[i]);
  ensures forall k :: 0 <= k < a.Length && k != i && k != j ==> a[k] == old(a[k]);
  ensures multiset(a[..]) == old(multiset(a[..]));
{
  var tmp := a[i];
  a[i] := a[j];
  a[j] := tmp;
}

lemma reverse_eq<T>(s1:seq<T>, s2:seq<T>)
  requires |s1| == |s2|;
  requires forall i :: 0 <= i < |s1| ==> s1[i] == s2[|s2| - 1 - i];
  ensures reverse(s1) == s2;
{
  if |s1| == 0 { } else {
    reverse_eq(s1[1..], s2[..|s2|-1]);    
  }
}

method Reverse<T>(a: array<T>)
  modifies a;
  ensures a[..] == reverse(old(a[..]));
{
  var i := 0;
  while (i <= a.Length - 1 - i)
    invariant 0 <= i <= a.Length - i + 1;
    invariant forall k :: i <= k <= a.Length - 1 - i ==>
      a[k] == old(a[k]);
    invariant forall k :: 0 <= k < i ==>
      a[a.Length - 1 - k] == old(a[k]) && a[k] == old(a[a.Length - 1 - k]);
  {
    Swap(a, i, a.Length - 1 - i);    
    i := i + 1;
  }
  assert forall i :: 0 <= i < a.Length ==> a[i] == old(a[a.Length - 1 - i]);
  reverse_eq(old(a[..]), a[..]);
}

method FindMax(a: array<int>) returns (max:int)
  requires a.Length >= 1;
  ensures 0 <= max < a.Length;
  ensures forall i :: 0 <= i < a.Length ==> a[i] <= a[max];
{ 
  var m := a[0]; 
  var r := 0;
  var i := 1;
  while (i < a.Length)
    invariant 1 <= i <= a.Length;
    invariant 0 <= r < a.Length;
    invariant m == a[r];
    invariant forall j :: 0 <= j < i ==> a[j] <= a[r];
  {
    if (a[i] > m) {
      r := i;
      m := a[i];
    }
    i := i + 1;
  }
  max := r; 
} 

method mean(x: int, y:int) returns (m : int)
  requires x % 2 == y % 2;
  ensures m == (x + y)/2;
{
  var i := x;
  var j := y;
  while (i != j)
    invariant i < j ==> (x + y)/2 - i == j - (x + y)/2;
    invariant i >= j ==> (x + y)/2 - j == i - (x + y)/2;
    decreases if i < j then j - i else i - j;
  {
    if (i < j) {
      i := i + 1;
      j := j - 1;
    } else {
      j := j + 1;
      i := i - 1;
    }
  }
  m := i;
}

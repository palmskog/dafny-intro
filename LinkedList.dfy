// Parametric linked lists
// Traditional (aclyclic) linked list implementation with a node containig 
// the list element and a reference to the rest of the list.
// Empty lists are represented simply by null. 
// Hence non-null values of type Node<T> represent non-empty lists.

module LinkedList {

  class Node<T(==)> {
    // abstract variable storing the list of elements in sequence (in the same order)
    ghost var list : seq<T>;

    // Heap frame, 
    // Consists of the set of nodes constituting the list headed by 'this'
    ghost var Repr : set<Node<T>>;

    // element stored in the node
    var elem : T;

    // next node in the list, if any
    var next : Node?<T>;

    // length of list
    var len : int;

    // The invariant predicate provides an inductive definition of 'list' and 'Repr'
    predicate Valid()
      reads this, Repr;
    {
      this in Repr &&
      (next == null ==> Repr == {this} && list == [elem]) &&
      (next != null ==>
        next in Repr && Repr == {this} + next.Repr &&
        this !in next.Repr &&
        list == [elem] + next.list &&
        next.Valid()) &&
      len == |list|
    }

    // Makes 'this' the head of a sigleton list containg element 'e'
    constructor Singleton(e: T)
      ensures Valid();
      ensures list == [e];
    {
      elem := e;
      next := null;
      len := 1;

      list := [e];
      Repr := {this};
    }

    // Makes 'this' the head of a non-sigleton list containg element 'e' 
    // and continuing with the list headed by 'n'
    constructor Insert(e: T, n: Node<T>)
      requires n.Valid();
      ensures Valid();
      ensures list == [e] + n.list;
      ensures Repr == {this} + n.Repr;
    {
      elem := e;
      next := n;
      len := 1 + n.len;

      list := [e] + n.list;
      Repr := {this} + n.Repr;
    }

    // Returns the (possibly empty) tail of the list headed by 'this'
    method Tail() returns (n: Node?<T>)
      requires Valid();
      ensures Valid();
      ensures n == null ==> |list| == 1;
      ensures n != null ==> n.Valid() &&
        n.Repr <= Repr &&
        n.list == list[1..];
    {
      n := next;
    }

    // Returns the element stored in the head of the list
    method Element() returns (e: T)
      requires Valid();
      ensures Valid();
      ensures e == list[0];
    {
      e := elem;
    }

    method Contains(e: T) returns (contains:bool)
      requires Valid();
      ensures Valid();
      ensures contains <==> e in list;
    {
      contains := false;
      var n := this;
      ghost var rem := list;
      ghost var elts := [];
      assert elts + rem == NodeSeq(n);
      while (n != null)
        invariant if n != null then n.Valid() else true;
        invariant rem == NodeSeq(n);
        invariant elts + rem == list;
        invariant contains <==> e in elts;
        decreases |rem|;
      {
        if e == n.elem {
          contains := true;
          break;
        } else {
          elts := elts + [n.elem];
          n := n.next;
          rem := NodeSeq(n);
        }
      }
    }

    method Size() returns (s:int)
      requires Valid();
      ensures Valid();
      ensures s == |list|;
    {
      s := len;
    }

    method List() returns (xs:seq<T>)
      requires Valid();
      ensures Valid();
      ensures xs == list;
    {
      xs := [];
      ghost var rem := list;
      var current := this;
      while (current != null)
        invariant current != null ==> current.Valid();
        invariant xs + rem == list;
        invariant rem == NodeSeq(current);
        decreases |rem|;
      {
        xs := xs + [current.elem];
        current := current.next;
        rem := NodeSeq(current);
      }
    }

  }

  method Append<T>(pre:Node<T>, post:Node<T>) returns (prepost:Node<T>)
    modifies pre.Repr;
    requires pre.Valid();
    requires post.Valid();
    requires pre.Repr !! post.Repr;
    ensures post.Valid();
    ensures prepost.Valid();
    ensures prepost.Repr <= old(pre.Repr) + old(post.Repr);
    ensures |prepost.list| == |old(pre.list)| + |old(post.list)|;
    ensures prepost.list == old(pre.list) + old(post.list);
  {
    var rev := Reverse(pre);
    ghost var revlist := rev.list;
    assert |revlist| == |old(pre.list)|;
    assert forall i :: 0 <= i < |revlist| ==> revlist[i] == old(pre.list)[|old(pre.list)|-1-i];
    var current := rev;
    prepost := post;
    ghost var elts := [];
    ghost var revelts := [];
    ghost var rem := revlist;
    assert elts + rem == revlist;
    while (current != null)
      invariant |revelts| == |elts|;
      invariant current != null ==>
        current.Valid() &&
        current in old(pre.Repr) &&
        current.Repr <= old(pre.Repr) &&
        current.Repr !! prepost.Repr;
      invariant prepost.list == revelts + post.list;
      invariant prepost.Valid();
      invariant prepost.Repr <= old(pre.Repr) + old(post.Repr);
      invariant elts + rem == revlist;
      invariant elts == revlist[..|elts|];
      invariant forall i :: 0 <= i < |elts| ==> elts[i] == old(pre.list)[|old(pre.list)|-1-i] && elts[i] == revelts[|elts|-1-i];
      invariant rem == NodeSeq(current);
      decreases if current != null then |current.list| else -1;
    {
      elts := elts + [current.elem];
      revelts := [current.elem] + revelts;
      var nx := current.next;
      current.next := prepost;
      current.len := 1 + prepost.len;
      current.list := [current.elem] + prepost.list;
      current.Repr := {current} + prepost.Repr;
      prepost := current;
      current := nx;
      rem := NodeSeq(current);
    }
    assert |elts| == |revelts|;
    assert |revlist| == |old(pre.list)|;
    assert elts == revlist;
    RevEqAll(revlist, old(pre.list), revelts);
    assert prepost.list == old(pre.list) + post.list;
  }

  method Reverse<T>(n:Node<T>) returns (reverse:Node<T>)
    modifies n.Repr;
    requires n.Valid();
    ensures reverse.Valid();
    ensures reverse.Repr <= old(n.Repr);
    ensures |reverse.list| == |old(n.list)|;
    ensures forall i :: 0 <= i < |reverse.list| ==> reverse.list[i] == old(n.list)[|old(n.list)|-1-i];
  {
    var current := n.next;
    reverse := n;
    reverse.next := null;
    reverse.len := 1;
    reverse.Repr := {reverse};
    reverse.list := [n.elem];
    while (current != null)
      invariant reverse.Valid() && reverse.Repr <= old(n.Repr);
      invariant current == null ==> |old(n.list)| == |reverse.list|;
      invariant current != null ==>
        current.Valid() &&
        current in old(n.Repr) && current.Repr <= old(n.Repr) &&
        current.Repr !! reverse.Repr;
     invariant current != null ==>
        |old(n.list)| == |reverse.list| + |current.list| &&
        current.list == old(n.list)[|reverse.list|..];
     invariant forall i :: 0 <= i < |reverse.list| ==> reverse.list[i] == old(n.list)[|reverse.list|-1-i];
     decreases if current != null then |current.list| else -1;
    {
      var nx := current.next;
      current.next := reverse;
      current.len := 1 + reverse.len;
      current.Repr := {current} + reverse.Repr;
      current.list := [current.elem] + reverse.list;
      reverse := current;
      current := nx;
    }
  }

  function NodeSeq<T>(n:Node?<T>) : seq<T>
    reads n;
    ensures n != null ==> NodeSeq(n) == n.list;
    ensures n == null ==> NodeSeq(n) == [];
  {
    if n != null then n.list else []
  }

  function NodeRepr<T>(n:Node?<T>) : set<Node<T>>
    reads n;
    ensures n != null ==> NodeRepr(n) == n.Repr;
    ensures n == null ==> NodeRepr(n) == {};
  {
    if n != null then n.Repr else {}
  }

  method FromSet<T>(s:set<T>) returns (n:Node?<T>)
    ensures s == {} ==> n == null;
    ensures s != {} ==> n != null;
    ensures n != null ==> n.Valid() && fresh(n.Repr);
    ensures forall i :: i in s <==> i in NodeSeq(n);
    ensures |NodeSeq(n)| == |s|;
  {
    if s == {} {
      n := null;
    } else {
      var x :| x in s;
      var n0 := FromSet(s - {x});
      if n0 != null {
        n := new Node.Insert(x, n0);
      } else {
        n := new Node.Singleton(x);
      }
    }
  }

  method FromSeq<T>(xs:seq<T>) returns (n:Node?<T>)
    ensures |xs| == 0 ==> n == null;
    ensures |xs| != 0 ==> n != null;
    ensures xs == NodeSeq(n);
    ensures n != null ==> n.Valid() && fresh(n.Repr);
  {
    if |xs| == 0 {
      n := null;
    } else if |xs| == 1 {
      n := new Node.Singleton(xs[0]);
    } else {
      var n' := FromSeq(xs[1..]);
      n := new Node.Insert(xs[0], n');
    }

  }

  lemma RevEqAll<T>(s0:seq<T>, s1:seq<T>, s2:seq<T>)
    requires |s0| == |s1|;
    requires |s0| == |s2|;
    requires forall i :: 0 <= i < |s0| ==> s0[i] == s1[|s0|-1-i] && s0[i] == s2[|s0|-1-i];
    ensures s1 == s2;
  {
    forall i | 0 <= i < |s0|
      ensures s1[i] == s2[i];
      {
        if s1[i] != s2[i] {
          var j := |s0|-1-i;
          assert |s0|-1-(|s0|-1-i) == i;
          assert s0[j] == s1[i];
          assert s0[j] == s2[i];
        }
      }
  }

}

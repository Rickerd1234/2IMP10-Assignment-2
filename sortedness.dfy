/* This note applies to the assignments on SlopeSearch, QuadraticSort, and Heapsort. 

   How to specify that an array of sequence is sorted (aka as ascending/descending)?
   In the assignments usually the "neighbor" or "local" approach is chosen, i.e.,
   each element is smaller than its neighbor, as follows. 
*/

predicate Sorted_LocalStyle(a: seq<int>)
{ forall i | 0 <= i < |a| - 1 :: a[i] <= a[i+1] }

/* Variants: <, >, >= instead of <= */

/* Another definition is what we call the "global" approach, i.e.,
   each element is smaller than each other element further in the sequence, as follows
*/

predicate Sorted_GlobalStyle(a: seq<int>)
{ forall i, j | 0 <= i < j < |a| :: a[i] <= a[j] }

/* It turns out that with the latter some Dafny proofs are easier, that is, 
   in the approaches I have seen. It depends on implementation, the choice and formulation 
   of invariants, etc.

   The two definitions are equivalent and you may use the one that suits you best. 
   So in this case you may change the given code. 
*/

/* As said, they are equivalent, and for those who are interested, here is the proof. */

// Local style and global style definitions of sortedness are equivalent
lemma LocalGlobalEquivalence(a: seq<int>)
  ensures Sorted_LocalStyle(a) <==> Sorted_GlobalStyle(a)
{
  if Sorted_LocalStyle(a) {
    Local2Global(a);
    assert Sorted_GlobalStyle(a);
  } 
  // following is not needed, but nice for the symmetry
  if Sorted_GlobalStyle(a) {
    assert Sorted_LocalStyle(a);
  }
}

// proof by induction to |a|
lemma Local2Global(a: seq<int>)
  requires Sorted_LocalStyle(a) 
  ensures  Sorted_GlobalStyle(a)
{ 
  if |a| < 2 {
    // no help needed
  } else {
    assert a[0] <= a[1];
    Local2Global(a[1..]);
  }
}

// not needed
lemma Global2Local(a: seq<int>)
  requires  Sorted_GlobalStyle(a)
  ensures Sorted_LocalStyle(a) 
{ 
  // no help needed
}

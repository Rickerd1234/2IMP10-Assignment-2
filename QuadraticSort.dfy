/** QuadraticSort
 * @name R.H.M. van Oosterhout - Q. Bakens
 * @id 1450131 - 1454315
 */

function Sorted(a: array<int>, low : nat, high : nat) : bool
   reads a;
   requires 0 <= low <= high <= a.Length;
{
   forall i :: low < i < high ==> a[i-1] <= a[i]
}

method {:verify true} QuadraticSort(a: array<int>)
   modifies a;
   ensures Sorted(a, 0, a.Length);
   ensures multiset(a[..]) == old(multiset(a[..]));
{
   if (a.Length == 0) {return;}
   var i := 1;
   while (i < a.Length)
      decreases a.Length - i
      invariant 0 < i <= a.Length
      invariant Sorted(a, 0, i)
      invariant multiset(a[..]) == old(multiset(a[..]))
   {
      var j := i-1;
      while (0 <= j && a[j] > a[j+1])
         decreases j
         invariant Sorted(a, 0, j+1)
         invariant 0 <= j < i - 1 ==> a[j] <= a[j + 2]
         invariant Sorted(a, j+1, i+1)
         invariant multiset(a[..]) == old(multiset(a[..])) 
      {
         a[j], a[j+1] := a[j+1], a[j];
         j := j - 1;
      }
      i := i + 1;
   }
}

// in the line below change true to false to free the prover from dealing with this method
method {:verify true} Test(a: array<int>) 
   modifies a
{
   // note: a[..] is the sequence (value type) 
   //       containing exactly the elemants of array a
   assume a[..] == [ 4, 3, 2, 1];
   QuadraticSort(a);
   assert a[..] == [1, 2, 3, 4];
}

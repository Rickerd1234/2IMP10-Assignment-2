// heapsort-start.dfy
// starter file for assignment 2imp10 y2021

/* Given is the basic structure of heapsort of an array
 * See Lecture slides for explanation of heapsort. 
 * 
 * Task: implement and verify the methods Heapify and HeapSort (last one is easy).
 * You can use the method UnHeapify. This will not lead to compilable code (since UnHeapify is
 * not implemented), but you should be able to produce verifying code. Furthermore, prove 
 * correct the lemma HeapMax.
 *
 * Notes:
    - The predicate sorted has an *inclusive* upperbound. This is different from our usual
      stance where we have upperbounds exclusive (and lowerbounds inclusive).
    - You may add methods, functions, predicates, and lemmas if you need them. 
    - When you add methods and lemmas, correctness should be proven, of course. 
      (The method UnHeapify may be left unproven.)
    - A bonus point can be earned when you do implement UnHeapify and prove it correct. 
 */

// a[lo..hi+1] is sorted
predicate sorted(a: array<int>, lo: int, hi: int)
  reads a
  requires 0 <= lo <= hi < a.Length
{
  forall j, k :: lo <= j < k <= hi ==> a[j] <= a[k]
}

// a upto and including index end represents a heap
predicate heap(a: array<int>, end: int)
  reads a
  requires 0 <= end < a.Length
{
  forall i :: 0 < i <= end ==> a[parent(i)] >= a[i]
}

predicate heapWithoutBubble(a: array<int>, end: int, skip: int)
  reads a
  requires 0 <= end < a.Length
{
  forall i :: (0 < i <= end && i != skip) ==> a[parent(i)] >= a[i]
}

// parent node id in the tree
function method parent(i: int) : int
{ (i - 1) / 2 }

// left child id in the tree
function method lchild(i: nat) : int
  ensures parent(lchild(i)) == i
{ 2 * i + 1 }

// right child id in the tree
function method rchild(i: nat) : int
  ensures parent(rchild(i)) == i
{ 2 * i + 2 }

// 0 is index of the maximum of a[0..i+1]
predicate firstmax(a: array<int>, i: int)
  reads a
  requires 0 <= i < a.Length
{
  forall k :: 0 <= k <= i ==> a[k] <= a[0]
}

// if a[..i+1] contains a heap, then a[0] is a maximal element of a[..i+1]
lemma {:verify true} HeapMax(a: array<int>, i: int)
  requires 0 <= i < a.Length
  requires heap(a, i)
  ensures firstmax(a, i)


// turn a into a heap by bubbling up
method {:verify true} Heapify(a: array<int>)
  modifies a;
  requires a.Length > 0;
  ensures heap(a, a.Length - 1);
  ensures multiset(a[..]) == multiset(old(a[..]));
  {
    var index: int := 1;
    while (true)
      decreases a.Length - index;
      invariant multiset(a[..]) == multiset(old(a[..]));
      invariant  1 <= index <= a.Length;
      // invariant heap(a, index - 1);
      // invariant firstmax(a, index);
      // invariant a[parent(parent(index))] > a[parent(index)];
      invariant forall i | 1 < i < index && parent(i) != 0 && parent(parent(i)) != 0 :: a[parent(parent(i))] > a[parent(i)];
    {
      if (index >= a.Length) {
        break;
      }

      assert heap(a, 0) ==> firstmax(a, 0);
      assert heap(a, 1) ==> firstmax(a, 1);

      var updateIndex := index;
      while (updateIndex > 0)
        decreases updateIndex;
        invariant multiset(a[..]) == multiset(old(a[..]));

        invariant heap(a, updateIndex) ==> firstmax(a, updateIndex - 1);
        // invariant 1 < updateIndex == index ==>  a[updateIndex] > a[parent(updateIndex)] || (heapWithoutBubble(a, updateIndex, updateIndex));
        // invariant 1 < updateIndex < index ==> a[updateIndex] > a[parent(updateIndex)] || (heapWithoutBubble(a, updateIndex, updateIndex));
        // invariant heapWithoutBubble(a, updateIndex, updateIndex)
        // invariant heap(a, updateIndex - 1);
      {
        var parentIndex: int := parent(updateIndex);       

        assert parentIndex < updateIndex;
        assert updateIndex != 0;
        assert heap(a, updateIndex) ==> a[lchild(0)] <= a[0];
        // assert  updateIndex == index ==> ((a[updateIndex] >= a[parent(updateIndex)]) || (heap(a, updateIndex)));

        if (a[updateIndex] > a[parentIndex]) {
          a[updateIndex], a[parentIndex] := a[parentIndex], a[updateIndex];
          assert a[updateIndex] <= a[parentIndex];
          updateIndex := parentIndex;
        } else {
          break;
        }
      }
      index := index + 1;
    }

  }


// turn a into a sorted array by putting the head of a to the end
// and insert the last element of the heap at the top and bubble it down
method {:verify true} UnHeapify(a: array<int>)
  modifies a
  requires a.Length > 0
  requires heap(a, a.Length - 1)
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures sorted(a, 0, a.Length - 1)

// sort a according to the heapsort algorithm
method {:verify true} HeapSort(a: array<int>)
  modifies a
  requires a.Length > 0
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures sorted(a, 0, a.Length - 1)
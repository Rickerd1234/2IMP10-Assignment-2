/** SlopeSearch
 * @name R.H.M. van Oosterhout - Q. Bakens
 * @id 1450131 - 1454315
 */

// slopesearch.dfy
// exercise SlopeSearch

predicate precon(f: seq<seq<nat>>, X: int)
{
  // F is non-empty and rectangular
  |f| > 0 && (forall i | 0 <= i < |f| :: |f[0]| == |f[i]| > 0)
  
  // All neighbors are increasing
  && (forall i | 0 <= i < |f| :: (forall j | 0 <= j < |f[i]|-1 :: f[i][j] <= f[i][j+1]))
  && (forall i | 0 <= i < |f|-1 :: (forall j | 0 <= j < |f[i]| :: f[i][j] <= f[i+1][j]))

  // Cells below (>i) and/or to the right (>j) are increasing
  // Equivalent to the properties above due to transitivity
  && (forall i,j | 0 <= i < |f| && 0 <= j < |f[i]| :: (forall r | 0 <= r < i:: f[r][j] <= f[i][j]))
  && (forall i,j | 0 <= i < |f| && 0 <= j < |f[i]| :: (forall c | 0 <= c < j:: f[i][c] <= f[i][j]))

  // X exists within f
  && (exists i,j | 0 <= i < |f| && 0 <= j < |f[i]| :: f[i][j] == X)
}

predicate postcon(f: seq<seq<nat>>, X:int, a: nat, b: nat)
{
  0 <= a < |f|
  && 0 <= b < |f[a]|
  && f[a][b] == X
}

method SlopeSearch(f: seq<seq<nat>>, X: int) returns (a: nat, b: nat)
  requires precon(f, X)
  ensures postcon(f, X, a, b)
{  
  a, b := 0, |f[0]|-1;

  while (true)
    decreases |f| - a + b
    invariant exists i,j | 0 <= i < |f| && 0 <= j < |f[i]| && f[i][j] == X :: 0 <= a <= i && j <= b < |f[i]|
  {
    if f[a][b] < X {
      a := a + 1;
    } else if f[a][b] > X {
      b := b - 1;
    } else {
      break;
    }
  }

  return a,b;
}

method SpecTest() {
  // Proof of incorrect precondition
  var matrix: seq<seq<nat>> := [[1,1], [2]];
  assert |matrix| == 2;
  assert |matrix[0]| == 2;
  assert |matrix[1]| == 1;

  matrix := [[1,1], [2,2]];
  assert |matrix| == 2;
  assert matrix[0][0] == 1;
  assert matrix[0][1] == 1;
  assert matrix[1][0] == 2;
  assert matrix[1][1] == 2;
  assert precon(matrix, 2);
  assert !precon(matrix, 3);

  matrix := [[3,2],[2,0]];
  assert matrix[0][0] == 3;
  assert matrix[0][1] == 2;
  assert matrix[1][0] == 2;
  assert matrix[1][1] == 0;
  assert !precon(matrix, 3);

  // Proof of correct precondition
  matrix := [[1,2], [2,2]];
  assert matrix[0][1] == 2;
  assert precon(matrix, 2);

  matrix := [[1,2,3],[2,2,4]];
  assert matrix[1][2] == 4;
  assert precon(matrix, 4);
}

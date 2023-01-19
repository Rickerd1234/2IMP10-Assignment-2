/** SlopeSearch
 * @name R.H.M. van Oosterhout - Q. Bakens
 * @id 1450131 - 1454315
 */

// slopesearch.dfy
// exercise SlopeSearch

// |a|-1 == M
// |a[0]|-1 == N

predicate rectseq(f: seq<seq<nat>>)
{
  |f| > 0 
  && |f[0]| > 0
  && (forall i | 0 < i < |f| :: |f[0]| == |f[i]|)
}

predicate neighinc?(f: seq<seq<nat>>, i: nat, j: nat)
  requires 0 <= i < |f| && 0 <= j < |f[i]|
{
  // Successors are increasing
  (i+1 < |f| && 0 <= j < |f[i+1]| ==> f[i][j] <= f[i+1][j])
  && (j+1 < |f[i]| && 0 <= i < |f| ==> f[i][j] <= f[i][j+1])

  // Predecessors are decreasing
  && (0 <= i-1 && 0 <= j < |f[i-1]| ==> f[i][j] >= f[i-1][j])
  && (0 <= j-1 && 0 <= i < |f| ==> f[i][j] >= f[i][j-1])
}

predicate precon(f: seq<seq<nat>>, X: int)
{
  // F is rectangular
  rectseq(f)
  // X exists within f
  && (exists i,j | 0 <= i < |f| && 0 <= j < |f[i]| :: f[i][j] == X)
  // Upper Left <= X <= Bottom Right
  && f[0][0] <= X <= f[|f|-1][|f[|f|-1]|-1]
  
  // All neighbors are decreasing or increasing properly
  && (forall i,j | 0 <= i < |f| && 0 <= j < |f[i]| :: neighinc?(f, i, j))
  
  // Everything above a cell with < X is also < X, below > X always > X
  && (forall i,j | 0 <= i < |f| && 0 <= j < |f[i]| && f[i][j] < X :: (forall c | 0 <= c < i:: f[c][j] < X))
  && (forall i,j | 0 <= i < |f| && 0 <= j < |f[i]| && f[i][j] > X :: (forall c | i < c < |f| :: f[c][j] > X))

  // Everything to the left of a cell  with < X is also < X, right > X always > X
  && (forall i,j | 0 <= i < |f| && 0 <= j < |f[i]| && f[i][j] < X :: (forall d | 0 <= d < j :: f[i][d] < X))
  && (forall i,j | 0 <= i < |f| && 0 <= j < |f[i]| && f[i][j] > X :: (forall d | j < d < |f[i]| :: f[i][d] > X))
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
  var M: nat := |f|-1;
  var N: nat := |f[0]|-1;
  
  a, b := 0, |f[0]|-1;

  assert exists i,j :: 0 <= i <= M && 0 <= j <= N && f[i][j] == X && 0 <= a <= i && j <= b <= N;

  while (true)
    decreases (M + N) - a + b
    invariant exists i,j | 0 <= i <= M && 0 <= j <= N && f[i][j] == X :: 0 <= a <= i && j <= b <= N
    // invariant exists i,j | a <= i <= M && 0 <= j <= b ::f[i][j] == X
  {
    if f[a][b] < X {
      // assert forall j | 0 <= j <= b :: f[a][j] < X;
      // assert exists i,j | 0 <= i <= M && 0 <= j <= N && f[i][j] < X :: 0 <= a <= i && j <= b <= N && f[a][j] < X;
      a := a + 1;
    } else if f[a][b] > X {
      // assert forall i | a <= i <= M :: f[i][b] > X;
      // assert exists i,j | 0 <= i <= M && 0 <= j <= N && f[i][j] > X :: 0 <= a <= i && j <= b <= N && f[i][b] > X;
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
  assert !rectseq(matrix);

  matrix := [[1,1], [2,2]];
  assert |matrix| == 2;
  assert rectseq(matrix);
  assert neighinc?(matrix,0,0);
  assert neighinc?(matrix,0,1);
  assert neighinc?(matrix,1,0);
  assert neighinc?(matrix,1,1);
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
  assert rectseq(matrix);
  assert !neighinc?(matrix, 0,0);
  assert !neighinc?(matrix, 1,1);
  assert !neighinc?(matrix, 0,0);
  assert !precon(matrix, 3);

  // Proof of correct precondition
  matrix := [[1,2], [2,2]];
  assert neighinc?(matrix,0,0);
  assert neighinc?(matrix,0,1);
  assert neighinc?(matrix,1,0);
  assert neighinc?(matrix,1,1);
  assert matrix[0][1] == 2;
  assert precon(matrix, 2);


  matrix := [[1,2,3],[2,2,4]];
  assert neighinc?(matrix,0,0);
  assert neighinc?(matrix,0,1);
  assert neighinc?(matrix,0,2);
  assert neighinc?(matrix,1,0);
  assert neighinc?(matrix,1,1);
  assert neighinc?(matrix,1,2);
  assert matrix[1][2] == 4;
  assert precon(matrix, 4);
}

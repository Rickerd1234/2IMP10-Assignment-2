// sumpositives.dfy
// exercise SumPositives


function sumpos(xs: seq<int>): int
{
  if |xs| == 0 then 0
  else if xs[0] > 0 then xs[0] + sumpos(xs[1..])
  else sumpos(xs[1..])
}

method SumPositives(xs: seq<int>) returns (s: int)
  ensures s == sumpos(xs)
{
  s := 0;
  if |xs| == 0 {
    return s;
  }

  var i: int;
  for i := 0 to |xs|
    invariant s + sumpos(xs[i..]) == sumpos(xs)
  {
    if (xs[i] > 0) {
      s := s + xs[i];
    }
  }

  return s;
}

method SpecTest() {
  assert sumpos([]) == 0;
  assert sumpos([-1]) == 0;
  assert sumpos([0]) == 0;
  assert sumpos([1]) == 1;
  assert sumpos([0,1,2,3]) == 6;
  assert sumpos([0,-1,2,-3]) == 2;
  assert sumpos([-40,10,0,0,-3,20,-3]) == 30;
}

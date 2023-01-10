// prime.dfy
// exercise Prime

predicate prime?(n: nat)
{
  n > 1 && forall d | 1 < d < n :: n % d != 0
}

method CheckPrime(n: nat) returns (p: bool)
  // ensures p <==> prime?(n)
{
  var i: nat;
  //TODO
  // no forall expressions in the executable code, only in spec and proof
}

method SpecTest() {
  assert prime?(2);
  assert !prime?(1);
  assert prime?(37);
  assert 74 % 2 == 0;
  assert !prime?(74);
}

/** Prime
 * @name R.H.M. van Oosterhout - Q. Bakens
 * @id 1450131 - 1454315
 */

// prime.dfy
// exercise Prime

predicate prime?(n: nat)
{
  n > 1 && forall d | 1 < d < n :: n % d != 0
}

method CheckPrime(n: nat) returns (p: bool)
  ensures p <==> prime?(n)
{
  var i: nat;
  // NOTE:
  // no forall expressions in the executable code, only in spec and proof
  if (n <= 1) {
    return false;
  }

  i := 2;
  while (i < n)
    // explicit termination
    decreases n - i
    // head invariant, every checked value (d) til now does not divide n
    invariant (forall d | 1 < d < i :: n % d != 0)
  {
    if (n % i == 0) {
      return false;
    }
    i := i + 1;
  }

  return true;
}

method SpecTest() {
  assert prime?(2);
  assert !prime?(1);
  assert prime?(37);
  assert 74 % 2 == 0;
  assert !prime?(74);
}

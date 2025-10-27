// Fails: postcondition claims 3*x, body computes 3*(x/2)

// @CheckError
method m(x: Int): Int
  requires x >= 0
  ensures result >= 0
  ensures result == 3 * x
{
  var acc: Int := 0;
  acc := x / 2;
  acc := acc * 6;
  return acc
}

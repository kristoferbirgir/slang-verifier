domain Pair {
  function pair(x: Int, y: Int): Pair
  function fst(x: Pair): Int
  function snd(x: Pair): Int

  axiom forall x: Int :: forall y: Int :: fst(pair(x,y)) == x
  axiom forall x: Int :: forall y: Int :: snd(pair(x,y)) == y
}

method bad_client(x: Int, y: Int)
{
  var xy: Pair := pair(x,y);
  
  // @CheckError
  assert fst(xy) == y  // This should fail - fst should equal x, not y
}
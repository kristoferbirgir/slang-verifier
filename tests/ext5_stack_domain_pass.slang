domain Stack {
  function empty(): Stack
  function push(s: Stack, x: Int): Stack
  function pop(s: Stack): Stack
  function top(s: Stack): Int
  function size(s: Stack): Int

  axiom size(empty()) == 0
  axiom forall s: Stack :: forall x: Int :: size(push(s, x)) == size(s) + 1
  axiom forall s: Stack :: forall x: Int :: top(push(s, x)) == x
  axiom forall s: Stack :: forall x: Int :: pop(push(s, x)) == s
}

method test_stack(): Int
  ensures result >= 0
{
  var s: Stack := empty();
  var s1: Stack := push(s, 10);
  var s2: Stack := push(s1, 20);
  
  assert size(s) == 0;
  assert size(s1) == 1;
  assert size(s2) == 2;
  assert top(s2) == 20;
  assert top(s1) == 10;
  
  return size(s2)
}
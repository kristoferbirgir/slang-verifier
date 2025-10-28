method unbounded_for_demo(n: Int): Int
    requires n >= 0
    ensures result >= 0
{
    var acc: Int := 0;
    for i in 1..(n + 1)
        invariant acc >= 0
    {
        acc := acc + 1
    };
    return acc
}
method unbounded_for_demo_fail(n: Int): Int
    requires n >= 0
    // @CheckError
    ensures result == 100  // This postcondition should fail
{
    var acc: Int := 0;
    for i in 1..(n + 1)
        invariant acc >= 0
    {
        acc := acc + 1
    };
    return acc
}
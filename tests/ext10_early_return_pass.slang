method simple_early_return_test(n: Int): Int
    requires n >= 0
    ensures result >= 0
{
    match {
        n == 0 => 
            return 5,
        true => 
            return n + 1
    };
    assert false  // not reachable, should pass
}
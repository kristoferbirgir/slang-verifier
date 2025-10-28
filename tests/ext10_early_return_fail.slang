method early_return_wrong_postcondition(x: Int): Int
    requires x >= 0
    // @CheckError  
    ensures result < 0  // This should fail - we always return non-negative values
{
    match {
        x == 0 => 
            return 0,
        true => 
            return x + 1
    };
    assert false  // unreachable
}
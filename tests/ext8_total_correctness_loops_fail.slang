method infinite_sum(n: Int): Int
    requires n >= 0
    ensures result >= 0
{
    var acc: Int := 0;
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant acc >= 0
        // @CheckError
        decreases n  // This should fail because n doesn't decrease in the loop
    {
        i < n =>
            i := i + 1;  // i increases but decreases clause is just n (constant)
            acc := acc + i
    };
    
    return acc
}
method client_fail(): Int
{
    var i: Int := 0;
    loop 
        invariant i >= 0
        // @CheckError
        invariant i <= 10  // This should fail because break happens at i == 15
    { true => 
        i := i + 1;
        match { i == 15 => 
            break 
        }
    };

    // @CheckError
    assert i == 10;  // This should fail because i == 15 when we break
    return i
}

method bad_continue(): Int
{
    var i: Int := 0;
    var sum: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= 10
        // @CheckError
        invariant sum <= 20  // This may not hold since sum could be 25
    { i < 10 => 
        i := i + 1;
        match { i % 2 == 0 => 
            continue
        };
        sum := sum + i
    };

    return sum
}
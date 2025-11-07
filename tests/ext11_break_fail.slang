// Extension Feature 11: Break statement - failing test
// This test should fail because the loop invariant is violated
method break_bad(): Int
{
    var i: Int := 0;
    loop 
        // @CheckError
        invariant i >= 0
        invariant i < 5  // This will be violated when i becomes 5
    { true => 
        i := i + 1;
        match { i == 10 => 
            break 
        }
    };
    return i
}

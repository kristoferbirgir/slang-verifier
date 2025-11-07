// Extension Feature 11: Break statement - passing test
// This test verifies that break statements can exit a loop early
method simple_break(): Int
    ensures result >= 0
{
    var i: Int := 0;
    loop 
        invariant i >= 0
    { true => 
        i := i + 1;
        match { i == 5 => 
            break 
        }
    };
    
    return i
}
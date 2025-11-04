method client(): Int
{
    var i: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= 15
    { true => 
        i := i + 1;
        match { i == 15 => 
            // The loop is interrupted. Execution resumes
            // from the first line after the loop.
            break 
        }
    };

    assert i == 15;
    return i
}

method test_continue(): Int
{
    var i: Int := 0;
    var sum: Int := 0;
    loop 
        invariant i >= 0
        invariant i <= 10
        invariant sum >= 0
    { i < 10 => 
        i := i + 1;
        match { i % 2 == 0 => 
            // Skip even numbers
            continue
        };
        sum := sum + i
    };

    assert sum == 25; // 1 + 3 + 5 + 7 + 9 = 25
    return sum
}
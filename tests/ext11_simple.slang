method simple_break(): Int
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
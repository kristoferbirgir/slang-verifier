method simple_no_break(): Int
{
    var i: Int := 0;
    loop 
        invariant i >= 0
    { i < 5 => 
        i := i + 1
    };
    
    return i
}
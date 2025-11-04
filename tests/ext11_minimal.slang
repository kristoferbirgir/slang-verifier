method test(): Int
{
    var i: Int := 0;
    loop 
        invariant i >= 0
    { i < 10 => 
        i := i + 1;
        match { i == 5 => break }
    };
    return i;
}
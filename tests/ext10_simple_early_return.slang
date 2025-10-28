method simple_early_return(x: Int): Int
    ensures result > 0
{
    match {
        x > 10 => 
            return x,
        x == 0 => 
            return 1,
        true => 
            return 5
    };
    // This line should be unreachable
    var unreachable: Int := 42;
    return unreachable
}
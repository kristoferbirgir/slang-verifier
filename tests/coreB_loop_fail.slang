method iter(n: Int): Int
    requires n >= 0
{
    var i: Int := 0;
    loop 
        // @CheckError
        // false: when the loop terminates, i == n + 1
        invariant i <= n 
    {
        i <= n => i := i + 1
    }
}
method simple_loop_fail() {
    var i: Int := 0;
    loop 
        // @CheckError
        invariant i <= 0
    {
        i <= 5 => i := i + 1
    }
}
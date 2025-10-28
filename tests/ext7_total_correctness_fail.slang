method infinite_loop(n: Int): Int
    requires n >= 0
    ensures result > 0
    // @CheckError
    decreases n  // This should fail because n doesn't decrease
{
    match {
        n == 0 => 
            return 1,
        true => 
            var res: Int;
            res := infinite_loop(n); // n doesn't decrease!
            return n * res
    }
}
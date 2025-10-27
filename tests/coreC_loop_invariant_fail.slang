// Test case 3: Loop invariant preservation failure
method test_loop_invariant_fail() {
    var i: Int := 0;
    loop 
        // @CheckError  
        invariant i <= 5
    {
        i < 10 => i := i + 1
    }
}
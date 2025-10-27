// Test case 4: Match branch assertion failure
method test_match_branch_fail(x: Int) {
    match {
        x > 0 => 
            // @CheckError
            assert x > 100,
        true => 
            assert true  // This should always pass
    }
}
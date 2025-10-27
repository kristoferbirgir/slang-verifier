// Test case 1: Assertion failure
method test_assertion_fail() {
    var x: Int := 5;
    // @CheckError
    assert x > 10
}
method client() {
    var acc: Int := 0;
    for i in 0..10 {
        acc := acc + i
    };
    // @CheckError
    assert acc == 50  // Should be 45, not 50
}
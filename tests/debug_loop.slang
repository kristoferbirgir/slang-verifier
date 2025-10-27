method simple_loop() {
    var i: Int := 0;
    loop 
        invariant i >= 0
    {
        i < 5 => i := i + 1
    }
}
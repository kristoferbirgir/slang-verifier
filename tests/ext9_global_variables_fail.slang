global counter: Int

method bad_inc()
    modifies counter
    // @CheckError  
    ensures counter == old(counter) + 2  // This should fail - we only increment by 1
{
    counter := counter + 1  // Only increments by 1, not 2
}

method test_bad(): Int
    requires counter >= 0
    modifies counter
    ensures result >= 0
{
    bad_inc();
    return counter
}
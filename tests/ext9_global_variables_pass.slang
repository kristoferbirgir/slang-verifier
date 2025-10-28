global counter: Int

method inc()
    modifies counter
    ensures counter == old(counter) + 1
{
    counter := counter + 1
}

method test_global(): Int
    requires counter >= 0
    modifies counter
    ensures result >= 1
    ensures counter >= 1
{
    inc();
    return counter
}
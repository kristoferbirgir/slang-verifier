global counter: Int

method test_old()
    modifies counter
    ensures counter == old(counter) + 5
{
    counter := counter + 5
}
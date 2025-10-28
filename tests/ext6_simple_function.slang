function double(x: Int): Int 
    requires true
    ensures result == 2 * x
{
    x + x
}

method test() {
    assert double(5) == 10
}
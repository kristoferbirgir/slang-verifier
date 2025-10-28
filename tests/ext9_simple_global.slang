global x: Int

method simple()
    modifies x
    ensures x == 42
{
    x := 42
}
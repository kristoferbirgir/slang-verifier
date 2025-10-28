function fac(n: Int): Int 
    requires n >= 0
    ensures result > 0
{
    n == 0 ? 1 : n * fac(n - 1)
}

method client() {
    assert fac(0) == 1
}
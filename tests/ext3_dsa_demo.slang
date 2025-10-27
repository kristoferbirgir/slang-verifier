method dsa_demo(x: Int): Int
    requires x > 0
    ensures result > x
{
    var y: Int := x + 1;
    return y
}
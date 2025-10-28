method factorial(n: Int): Int
    requires n >= 0
    ensures result > 0
    decreases n
{
    match {
        n == 0 => 
            return 1,
        true => 
            var res: Int;
            res := factorial(n - 1);
            return n * res
    }
}
method m(x: Int): Int {
  return x + 1
}
// @CheckError
ensures result == x + 2

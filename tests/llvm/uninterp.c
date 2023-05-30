int uninterp(int i, int j) { return i; }

int test(int i, int j) {
  return uninterp(i, i) + uninterp(j, j);
}

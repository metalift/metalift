// code from Barnett et al's PASTE 2005 paper, "Weakest-Precondition of Unstructured Programs"

int test(int x) {
  while (0 < x) {
    x = x - 1;
  }
  return x;
}

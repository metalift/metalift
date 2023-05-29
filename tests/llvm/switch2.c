// test the ability to merge multiple paths assigning the same value to a variable
int test(int arg) {
  int r;
  switch(arg) {
    case 1: r = 10; break;
    case 2: r = 10; break;
    case 3: r = 20; break;
    default: r = 20; break;
  }

  return r;
}

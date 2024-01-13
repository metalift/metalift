int test()
{
  int x = 0;
  int y = 0;

  while(y<3){

    int z = 0;
    while (z<5) {
      x = x+2;
      z = z+1;
    }
    y = y+1;
  }

  return x;
}

int test()
{
  int x = 0;
  int y = 1;

  while(y<3){
    x = x+y;
    y = y+1;
  }

  int z = 1;

  while(z<4){
    x = x+z;
    z = z+1;
  }

  return x;
}

int test(int x)
{
	int y = 0;
	
  // inv: y <= x or y = 0
	while (y<x){
		y = y+1;
	}

  // ps: y = x or y = 0
  return y;
}

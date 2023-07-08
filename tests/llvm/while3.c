int test(int arg)
{
	int x = 0;
	int y = 1;

	while(y<arg){
		x = x+y;
		y = y+1;
	}

  return x;
}


arg = 0 -> 0
arg = 1 -> 1
arg = 2
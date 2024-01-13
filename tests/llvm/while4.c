// same as while3.c except with loop run for exactly 3 times
int test()
{

	int x = 0;
	int y = 1;

	while(y<3){
		x = x+y;
		y = y+1;
	}

  return x;
}

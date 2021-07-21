#include <stdio.h>

int sum_n (int x) {
  if (x >= 1) return (x + sum_n(x - 1));
  else return 0;
}

int main(int argc, char** argv)

{
	int arg = 1;
	int x = 0;
	int y = 0;
	
	while(y<arg){
		x = x+y;
		y = y+1;
	}

  printf("x = %d, sum = %d, arg = %d\n", x, sum_n(arg - 1), arg);
  return x;
}



/*
{
	
	int x = 0;
	int y = 1;
	
	while(y<3){
		x = x+y;
		y = y+1;
    printf("x= %d y= %d\n", x, y);
	}

  return x;
}
*/

int  main()
{
	
	int x = 0;
	int y = 1;
	
	while(y<=3){
		x = x+y;
    if (x > 5) {
  		y = y+1;
      continue;
    }
    else
      y = y + 2;
	}

  return x;
}

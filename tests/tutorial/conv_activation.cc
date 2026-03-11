
int conv_activation(int bias, int weight, int input)
{
    int result = bias + weight * input;  
    if (result < 0) result = 0;          
    return result;
}


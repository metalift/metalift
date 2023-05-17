int test(int a, int b) {
    int result = 0;
    // First we calculate abs(a)
    int abs_a;
    if (a < 0) {
        result += -a;
    } else {
        result += a;
    }
    // Then we want to add abs(a + b)
    int abs_ab_sum;
    if (a + b < 0) {
        abs_ab_sum = - (a + b);
    } else {
        abs_ab_sum = a + b;
    }
    result += abs_ab_sum;
    
    // Then add abs(a + b + b + b)
    int d = a + b + b + b;
    if (d < 0) {
        d = -d;
    } 
    result += d;
    return result;
}
extern int __VERIFIER_nondet_int(void);

//CTL ([EF](p==0)) && ([EF](p==1))

int main() {
    int k, y, x, c;
    // k = __VERIFIER_nondet_int();

    y = 0;
    x = 0;
    // c = 0;

    int p;
    p = 2;
 
    while (1) {
        // __VERIFIER_assert(-2*y*y*y*y*y*y - 6 * y*y*y*y*y - 5 * y*y*y*y + y*y + 12*x == 0);

        if (!(c + -2*y*y*y*y*y*y - 6 * y*y*y*y*y - 5 * y*y*y*y + y*y + 12*x < k))
            break;

        c = c + 1;
        y = y + 1;
        x = y * y * y * y * y + x;

        p = 1;
  
    }

    p = c+k;

    // __VERIFIER_assert(-2*y*y*y*y*y*y - 6 * y*y*y*y*y - 5 * y*y*y*y + y*y + 12*x == 0);
    // __VERIFIER_assert(k*y == y*y);      
    return 0;
}


extern int __VERIFIER_nondet_int(void);

//CTL ([EF](p==0)) && ([EF](p==1))

int main() {
    int k, y, x, c;
    k = __VERIFIER_nondet_int();

    y = 0;
    x = 0;
    c = 0;

    int p;
    p = 2;

    while (1) {
        // __VERIFIER_assert(6*x - 2*y*y*y - 3*y*y - y == 0);

        if (!(c + 6*x - 2*y*y*y - 3*y*y - y < k))
            break;

        c = c + 1;
        y = y + 1;
        x = y * y + x;
        p = 1;
   
    }
    // __VERIFIER_assert(6*x - 2*y*y*y - 3*y*y - y == 0);
    p = c + k;
    return 0;
}

/* 
Geometric Series
computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
*/
extern int __VERIFIER_nondet_int(void);

//CTL ([EF](p==0)) && ([EF](p==1))
// ARGS: -precondition "c == 0 && c < k" -domain polyhedra

int main() {
    int z, k;
    int x, y, c;
    z = __VERIFIER_nondet_int();
    // k = __VERIFIER_nondet_int();

    x = 1;
    y = 1;
    /* c = 1; */
    // c = 0;

    int p;
    p = 2;
    while (1) {
        // __VERIFIER_assert(1 + x*z - x - z*y == 0);

        if (!(1 + x*z - x - z*y + c < k))
            break;

        c = c + 1;
        x = x * z + 1;
        y = y * z;

        p = 1;
    }

    p = 0;
    // __VERIFIER_assert(1 + x*z - x - z*y == 0);
    return 0;
}


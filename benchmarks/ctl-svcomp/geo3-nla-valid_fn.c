/* 
Geometric Series
computes x = sum(z^k)[k=0..k-1], y = z^(k-1)
*/
// extern int __VERIFIER_nondet_int(void);
//CTL ([EF](p==0)) && ([EF](p==1))
// ARGS: -precondition "c == 1 && c < k" -domain polyhedra

int main() {
    int z, a, k;
    int x, y, c;
    z = ?;
    a = ?;
    // k = __VERIFIER_nondet_int();

    x = a;
    y = 1;
    // c = 1;

    int p;
    p = 2;
    while (1) {
        // __VERIFIER_assert(z*x - x + a - a*z*y == 0);

        if (!(z*x - x + a - a*z*y + c < k))
            break;

        c = c + 1;
        x = x * z + a;
        y = y * z;

        p = 1;
    }

    p = 0;
    // __VERIFIER_assert(z*x - x + a - a*z*y == 0);
    return x;
}

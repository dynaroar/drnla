/*
  hardware integer division program, by Manna
  returns q==A//B
  */

extern int __VERIFIER_nondet_int(void);

int main() {
    int A, B;
    int r, d, xp, q;
    A = __VERIFIER_nondet_int();
    B = __VERIFIER_nondet_int();
    //assume_abort_if_not(B >= 1);
    if (B < 1) return 0;

    r = A;
    d = B;
    xp = 1;
    q = 0;
    int p = 2;
    while (1) {
        // __VERIFIER_assert(q == 0);
        // __VERIFIER_assert(r == A);
        // __VERIFIER_assert(d == B * p);
        if (!(r >= B * xp)) break;

        d = 2 * d;
        xp = 2 * xp;
    }
    p = 1;
    while (1) {
        // __VERIFIER_assert(A == q*B + r);
        // __VERIFIER_assert(d == B*p);

        if (!(A - q*B - r + xp != 1)) break;

        d = d / 2;
        xp = xp / 2;
        if (r >= d) {
            r = r - d;
            q = q + xp;
        }
    }
    p = 0;
    // __VERIFIER_assert(A == d*q + r);
    // __VERIFIER_assert(B == d);    
    return 0;
}

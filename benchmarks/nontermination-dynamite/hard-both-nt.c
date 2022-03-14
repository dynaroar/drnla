/*
  hardware integer division program, by Manna
  returns q==A//B
  */

extern int __VERIFIER_nondet_int(void);

int main() {
    int A, B;
    int r, d, p, q;
    A = __VERIFIER_nondet_int();
    B = __VERIFIER_nondet_int();
    //assume_abort_if_not(B >= 1);
    if (B < 1) return 0;

    r = A;
    d = B;
    p = 1;
    q = 0;

    while (1) {
        // __VERIFIER_assert(q == 0);
        // __VERIFIER_assert(r == A);
        // __VERIFIER_assert(d == B * p);
        if (!(d == B * p)) break;

        d = 2 * d;
        p = 2 * p;
    }

    while (1) {
        // __VERIFIER_assert(A == q*B + r);
        // __VERIFIER_assert(d == B*p);

        if (!(A == q*B + r)) break;

        d = d / 2;
        p = p / 2;
        if (r >= d) {
            r = r - d;
            q = q + p;
        }
    }

    // __VERIFIER_assert(A == d*q + r);
    // __VERIFIER_assert(B == d);    
    return 0;
}

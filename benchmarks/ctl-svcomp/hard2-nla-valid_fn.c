/*
  hardware integer division program, by Manna
  returns q==A//B
  */

// extern int __VERIFIER_nondet_int(void);

// ARGS: -domain polyhedra

int main() {
    int A, B;
    int r, d, p, q;
    A = ?;
    B = 1;

    r = A;
    d = B;
    xp = 1;
    q = 0;
    int p = 2;
    while (1) {
        // __VERIFIER_assert(q == 0);
        // __VERIFIER_assert(r == A);
        // __VERIFIER_assert(d == B * p);
        if (!(B * xp - d + r >= d)) break;

        d = 2 * d;
        p = 2 * p;
    }
    p = 1;
    while (1) {
        // __VERIFIER_assert(A == q*B + r);
        // __VERIFIER_assert(d == B*p);

        if (!(B * xp - d + r >= d)) break;

        d = d / 2;
        p = p / 2;
        if (r >= d) {
            r = r - d;
            q = q + p;
        }
    }
    p = 0;
    // __VERIFIER_assert(A == d*q + r);
    // __VERIFIER_assert(B == d);    
    return 0;
}

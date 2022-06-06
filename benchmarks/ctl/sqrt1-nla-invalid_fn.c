// https://github.com/sosy-lab/sv-benchmarks/blob/master/c/nla-digbench/sqrt1.c
/* Compute the floor of the square root of a natural number */

//CTL ([EF](p==0)) && ([EF](p==1))

extern int __VERIFIER_nondet_int(void);

int main() {
    int n, a, s, t, k, c;
    n = __VERIFIER_nondet_int();
    // k = __VERIFIER_nondet_int();

    a = 0;
    s = 1;
    t = 1;
    // c = 0;

    int p;
    p = 2;
    
    while (t*t - 4*s + 2*t + 1 + c <= k) {
        //__VERIFIER_assert(t == 2*a + 1);
        //__VERIFIER_assert(s == (a + 1) * (a + 1));
        //__VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);
        // the above 2 should be equiv to 
        //if (!(s <= n))break;
        a = a + 1;
        t = t + 2;
        s = s + t;
	c = c + 1;

        p = 1;
    }

    p = a-k;
    //__VERIFIER_assert(t == 2 * a + 1);
    //__VERIFIER_assert(s == (a + 1) * (a + 1));
    //__VERIFIER_assert(t*t - 4*s + 2*t + 1 == 0);

    return 0;
}

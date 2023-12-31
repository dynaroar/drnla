/* extended Euclid's algorithm */
// extern int __VERIFIER_nondet_int(void);

// ARGS: -precondition "x>=1 && y>=1" -domain polyhedra

int main() {
    int a, b, xp, q, r, s;
    int x, y;
    // x = __VERIFIER_nondet_int();
    // y = __VERIFIER_nondet_int();
    //assume_abort_if_not(x >= 1);
    //assume_abort_if_not(y >= 1);

    int p = 2;
    if (x>=1 && y>=1) {
        a = x;
        b = y;
        xp = 1;
        q = 0;
        r = 0;
        s = 1;
   
        while (y * r + x * xp != x * q + y * s) {
            //__VERIFIER_assert(1 == p * s - r * q);
            //__VERIFIER_assert(a == y * r + x * p);
            //__VERIFIER_assert(b == x * q + y * s);

            if (a > b) {
                a = a - b;
                xp = xp - q;
                r = r - s;
            } else {
                b = b - a;
                q = q - p;
                s = s - r;
            }

            p = 1;
        }
    
    	//__VERIFIER_assert(a - b == 0);    
    	//__VERIFIER_assert(p*x + r*y - b == 0);
    	//__VERIFIER_assert(q*r - p*s + 1 == 0);
    	//__VERIFIER_assert(q*x + s*y - b == 0);
        p = 0;
    }
    return 0;
}

/* extended Euclid's algorithm */
// extern int __VERIFIER_nondet_int(void);

// ARGS: -precondition "x>=1 && y>=1" -domain polyhedra

int main() {
    int x, y;
    int a, b, xp, q, r, s, c, k;
    // x = __VERIFIER_nondet_int();
    // y = __VERIFIER_nondet_int();
    int p = 2;
    //assume_abort_if_not(x >= 1);
    if (x<1) {
	return x;
    }
    //assume_abort_if_not(y >= 1);
    if (y < 1) {
	return x;
    }

    a = x;
    b = y;
    xp = 1;
    q = 0;
    r = 0;
    s = 1;
    c = 0;
    k = 0;
    while (1) {
        if (!(b != 0))
            break;
        c = a;
        k = 0;

        while (c >= b) {
            //__VERIFIER_assert(a == k * b + c);
            //__VERIFIER_assert(a == y*r + x*p);
            //__VERIFIER_assert(b == x * q + y * s);
	    //__VERIFIER_assert(q*x*y + s*y*y - q*x - b*y - s*y + b == 0);
            c = c - b;
            k = k + 1;
        }
        p = 1;
        a = b;
        b = c;

        int temp;
        temp = xp;
        xp = q;
        q = temp - q * k;
        temp = r;
        r = s;
        s = temp - s * k;
    }
    
    p = c-b+1;
    //__VERIFIER_assert(q*x + s*y == 0);
    //__VERIFIER_assert(p*x + r*y == a);
    return a;
}

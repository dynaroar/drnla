extern int __VERIFIER_nondet_int(void);

//CTL [AF]([AG](p>0))  


int main() {
    int a, n, x, y, z;
    a = __VERIFIER_nondet_int();
    n = 0;
    x = 0;
    y = 1;
    z = 6;
    int c = 0, k = __VERIFIER_nondet_int();

    int p, xp;
    p = 0;
    xp = __VERIFIER_nondet_int();

    if (xp > 0) {
        p = p+1;
    }
    else {
        while ((z*z) - 12*y - 6*z + 12 + c <= k) {
            n = n + 1;
            x = x + y;
            y = y + z;
            z = z + 6;
            c = c + 1;
        }
        p = 1;
  }
    /* while(1) { if(dummy>0) break; } L_return: return 0; */

    return 0;
}

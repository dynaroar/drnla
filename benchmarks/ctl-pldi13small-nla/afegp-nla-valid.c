//CTL [AF]([EG](p>0)) 

extern int __VERIFIER_nondet_int(void);

int main() {
    int n, a, s, t, k, c;
    n = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();

    a = 0;
    s = 1;
    t = 1;
    c = 0;

    int p, rho, x;
    p = 0;
    x = 5;
    
    while (t*t - 4*s + 2*t + 1 + c <= k) {
        a = a + 1;
        t = t + 2;
        s = s + t;
	c = c + 1;
     }
    p = 1;
    while(1) {
        rho = __VERIFIER_nondet_int();
        if ( rho > 0) {
            p = 0;
        }
    }

    /* while(1) { if(dummy>0) break; } L_return: return 0; */
    
    return 0;
}

extern int __VERIFIER_nondet_int(void);

//CTL [EG]([AG](p<=0))  


int main() {
    int x, y, z;
    z = __VERIFIER_nondet_int();
    x = 1;
    y = 1;

    int c = 0, k = __VERIFIER_nondet_int();

    int p, xp, rho1;
    p = 0;
    xp = 5;
    while (1 + x*z - x - z*y + c < k) {
        c = c + 1;
        x = x*z + 1;
        y = y*z;
    }

    while(xp>=0){
        rho1 = __VERIFIER_nondet_int();

        if (rho1>0){
            xp = xp-1;
        }

    }

    p=1;
    /* while(1) { if(dummy>0) break; } L_return: return 0; */

    return 0;
}

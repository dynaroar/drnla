extern int __VERIFIER_nondet_int(void);

//CTL ([AF]([AG](p>0))) 


int main() {
    int k, y, x, c, z, nd;
    z = __VERIFIER_nondet_int();
    k = __VERIFIER_nondet_int();

    y = z;
    x = 1;
    c = 1;

    int p;
    p = 0;
    
    while (1) {
         if (!(c < k))
            break;

        c = c + 1;
        x = x * z + 1;
        y = y * z;
     }

    while(1) {
        nd = __VERIFIER_nondet_int();
        if (nd > 0)
            p = 1;
        else 
            p = 2;
    }
    /* while(1) { if(dummy>0) break; } return 0; */
    return 0;
}

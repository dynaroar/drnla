extern int __VERIFIER_nondet_int(void);

//CTL [EG](p<=0)  


int main() {
    int k, y, x, c;
    k = __VERIFIER_nondet_int();

    y = 0;
    x = 0;
    c = 0;

    int p;
    p = 0;
    
    while (c + 6*x - 2*y*y*y - 3*y*y - y < k) {
        c = c + 1;
        y = y + 1;
        x = y * y + x;
     }
    p = 1;
     
    /* while(1) { if(dummy>0) break; } L_return: return 0; */

    return 0;
}

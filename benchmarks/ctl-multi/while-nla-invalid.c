extern int __VERIFIER_nondet_int(void);
int main() {
    int x, y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    int p = 2;
    while(y>0){

        if (x*x - 2*x >= 63) y = y-2;
        y--;
        p = 1;
    }
    p = y-1;
    return 0;
}

extern int __VERIFIER_nondet_int(void);
int main() {
    int x, y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    int p = 2;
    while((x*x*x < 27) && (y*y*y >=8)){

        /* if (x*x*x>27) y = y-2; */
        y --;
        x--;
        p = 1;
    }
    p = y-2;
    return 0;
}

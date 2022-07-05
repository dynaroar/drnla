extern int __VERIFIER_nondet_int(void);
int main() {
    int x, y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();

    while((x*x*x < 27) && (y*y*y >=8)){

        /* if (x*x*x>27) y = y-2; */
        y --;
        x--;
    }
    
    return 0;
}

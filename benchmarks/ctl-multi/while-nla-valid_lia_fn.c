// extern int __VERIFIER_nondet_int(void);

// ARGS: -domain polyhedra

int main() {
    int x, y;
    // x = __VERIFIER_nondet_int();
    // y = __VERIFIER_nondet_int();
    x = ?;
    y = ?;
    int p = 2;
    while(y>0){

        if ((x>=9) || (x<=-7)) y = y-2;
        y--;
        p = 1;
    }
    p = 0;
    return 0;
}

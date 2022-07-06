// extern int __VERIFIER_nondet_int(void);

// ARGS: -domain polyhedra

int main() {
    int x, y;
    // x = __VERIFIER_nondet_int();
    // y = __VERIFIER_nondet_int();
    x = ?;
    y = ?;
    int p = 2;
    while (y>0){
        if (x*x>49) y = y-5;
        y--;
        p = 1;
    }
    p = 0;
    return x;
}

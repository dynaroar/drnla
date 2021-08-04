int mainF(int x, int y) {
    int px, py;
    int dup = 0;
   
    __VERIFIER_assume(y > 0);
    __VERIFIER_assume(x > y);
    __VERIFIER_assume(x > 0);
    
    if (y == 0) return 1;
    while (x > 0) {
        if (y == 0) return 1;
        if (dup) {
            if (!(px > y && px >= 0))
                return 0;
        }
        if (!dup && __VERIFIER_nondet_int()) {
            px = x;
            py = y;
            dup = 1;
        }
        x--;
        y--;
    }
    if (y == 0) return 1;
    return 0;
}

int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    int r = mainF(x, y);
    //@ assert (r == 1);
}

/*
// AF(y == 0)
int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    
    __VERIFIER_assume(y > 0);
    __VERIFIER_assume(x > y);
    __VERIFIER_assume(x > 0);
    
    while (x > 0) {
        x--;
        y--;
    }
}
*/

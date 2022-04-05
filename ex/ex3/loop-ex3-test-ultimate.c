//@ ltl invariant positive:  <>(AP(term == 1));

int fail; int term;
int agree_sign = 0;
int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    __VERIFIER_assume(x != 0 && y != 0);

    while( (x<0 && y>0) || (y<0 && x>0) ) {
    //while (x * y < 0) {
      x = x + 1;
      y = y + 1;
    }
    term = 1;
    return 0;
}

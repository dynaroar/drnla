//https://github.com/letonchanh/dynamite/blob/master/benchmarks/nla-term/cohencu1-both-t.c

//@ ltl invariant positive: [](<>AP(y == 0));
int __VERIFIER_nondet_int(void){}

int a, n, x, y, z;
int main() {
    a = __VERIFIER_nondet_int();
    n = 0;
    x = 0;
    y = 1;
    z = 6;
    int k = __VERIFIER_nondet_int();
    while (1){
        /* while (6 * n + 6 <= k) { */
        while (3 * n * n + 3 * n + 1 <= k) {
            n = n + 1;
            x = x + y;
            y = y + z;
            z = z + 6;
        }
        y = 0;
    }
    return 0;
}

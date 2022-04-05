//@ ltl invariant positive: <>(AP(term == 1));

int term = 0;
int main() {
    int n, x, y, z, k;
    n = 0;
    x = 0;
    y = 1;
    z = 6;
    k = __VERIFIER_nondet_int();
    while (3 * n * n + 3 * n + 1 <= k) { // y <= k
        n = n + 1;
        x = x + y;
        y = y + z;
        z = z + 6;
    }
    term = 1;
    return 0;
}

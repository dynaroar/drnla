//CTL [AF]([AG](p>0))  
// ARGS: -precondition "c == 0 && c <= k" -domain polyhedra

int main() {
    int a, n, x, y, z;
    a = ?;
    n = 0;
    x = 0;
    y = 1;
    z = 6;
    int c, k;
    // int c = 0, k = __VERIFIER_nondet_int();

    int p, xp;
    p = 0;
    xp = ?;

    if (xp > 0) {
        while(1) {
            p = p+1;
        }
    }
    else {
        while (c <= k) {
            n = n + 1;
            x = x + y;
            y = y + z;
            z = z + 6;
            c = c + 1;
        }
        p = 0;
    }
    /* while(1) { if(dummy>0) break; } L_return: return 0; */

    return 0;
}

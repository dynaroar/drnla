//CTL ([AF]([AG](p>0))) 
// ARGS: -precondition "c == 0 && c < k" -domain polyhedra

int main() {
    int k, y, x, c, nd;
    // k = __VERIFIER_nondet_int();

    y = 0;
    x = 0;
    // c = 0;

    int p;
    p = 0;
    
    while (1) {
         if (!(c + (y * y) - 2 * x + y < k))
            break;

        c = c + 1;
        y = y + 1;
        x = y + x;
     }

    while(1) {
        nd = ?;
        if (nd > 0)
            p = 1;
        else 
            p = 2;
    }
    /* while(1) { if(dummy>0) break; } return 0; */
    return 0;
}

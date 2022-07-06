//CTL ([AF]([AG](p>0))) 
// ARGS: -precondition "c == 0 && c < k" -domain polyhedra

int main() {
    int k, y, x, c, z, nd;
    // k = __VERIFIER_nondet_int();

    z = ?;
    k = ?;
    y = z;
    x = 1;
    c = 1;

    int p;
    p = 0;
    
    while (1) {
        //__VERIFIER_assert(x*z - x - y + 1 == 0);

        if (!(x*z - x - y + 1 + c < k)) 
            break;

        c = c + 1;
        x = x * z + 1;
        y = y * z;
 
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

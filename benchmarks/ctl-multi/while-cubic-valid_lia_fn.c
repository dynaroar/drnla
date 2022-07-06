// extern int __VERIFIER_nondet_int(void);

// ARGS: -domain polyhedra

int main() {
    int y;
    // y = __VERIFIER_nondet_int();
    y = ?;
    int p = 2;
    while( y <= 4 && (y>=1 || y<=-1)){
         y++;
         p = 1;
    }
    p = 0;
    return 0;
}

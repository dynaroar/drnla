// extern int __VERIFIER_nondet_int(void);

// ARGS: -domain polyhedra

int main() {
    int x;
    int p = 2;
    // x = __VERIFIER_nondet_int();
    x = ?;
    if (x*x*x == 8){
          p = 1;
        return 1;
    } else{
          p = x-2;
        return 0;
    }
}

// extern int __VERIFIER_nondet_int(void);

// ARGS: -domain polyhedra

int main() {
    int x;
    int p = 2;
    // x = __VERIFIER_nondet_int();
    x = ?;
    if (x<=2 && x>= 2){
          p = 1;
        return 1;
    } else{
          p = 0;
        return 0;
    }
}

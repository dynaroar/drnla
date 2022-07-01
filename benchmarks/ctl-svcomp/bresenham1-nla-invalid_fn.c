/*
  Bresenham's line drawing algorithm 
  from Srivastava et al.'s paper From Program Verification to Program Synthesis in POPL '10 
*/
/*
extern void __VERIFIER_error() __attribute__((__noreturn__));
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_assume(int expression);
void __VERIFIER_assert(int cond) {
    if (!(cond)) {
    ERROR:
        __VERIFIER_error();
    }
    return;
}
*/

//CTL ([EF](p==0)) && ([EF](p==1))
// ARGS: -precondition "c == 0 && c <= k" -domain polyhedra

// extern int __VERIFIER_nondet_int(void);
int main() {
    int X, Y;
    int v, x, y;
    // X = __VERIFIER_nondet_int();
    // Y = __VERIFIER_nondet_int();
    X = ?;
    Y = ?;
    v = 2 * Y - X;
    y = 0;
    x = 0;
    int c, k;
    //c = 0;
    //k = __VERIFIER_nondet_int();
    int p;
    p = 2;

    while (2*Y*x - 2*X*y - X + 2*Y - v + c <= k) {
      //__VERIFIER_assert(2*Y*x - 2*X*y - X + 2*Y - v == 0);
      //if (!(x <= X))            break;
        // out[x] = y

        if (v < 0) {
            v = v + 2 * Y;
        } else {
            v = v + 2 * (Y - X);
            y++;
        }
        x++;
        c++;
        p = 1;
    }
    //__VERIFIER_assert(2*Y*x - 2*x*y - X + 2*Y - v + 2*y == 0);
    p = x-k;
    return 0;
}

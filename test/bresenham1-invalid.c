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


//extern int __VERIFIER_nondet_int(void);
void main() {
    int X, Y;
    int v, x, y;
    X = read();
    Y = read();
    v = 2 * Y - X;
    y = 0;
    x = 0;
    int c, k;
    c = 0;
   /* k = read(); */
      k = 0;
    int p;
    p = 2;

  //  while (2*Y*x - 2*X*y - X + 2*Y - v + c <= k) {
    while (c <= k-1) {
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
   // c == x; c>k

//    p = x-k;
    if (p != 1) {
      print(p);
      }
//    print(p);
    return;
}

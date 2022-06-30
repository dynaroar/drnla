/* shift_add algorithm for computing the 
   product of two natural numbers
*/
extern int __VERIFIER_nondet_int(void);

int main() {
    int a, b;
    int x, y, z;

    a = __VERIFIER_nondet_int();
    b = __VERIFIER_nondet_int();
    // assume_abort_if_not(b >= 1);

    if (b < 1) {
        return 0;
    }

    x = a;
    y = b;
    z = 0;

    int p = 2;

    while (1) {
        // __VERIFIER_assert(z + x * y == a * b);
        if (!(y + z + x * y - a * b != 0))
            break;

        if (y % 2 == 1) {
            z = z + x;
            y = y - 1;
        }
        x = 2 * x;
        y = y / 2;
        p = 1;
    }
    // __VERIFIER_assert(z == a * b);

    p = 0;
    return 0;
}

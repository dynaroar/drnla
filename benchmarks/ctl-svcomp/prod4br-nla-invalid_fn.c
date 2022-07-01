/* algorithm for computing the product of two natural numbers */

// extern int __VERIFIER_nondet_int(void);

// ARGS: -precondition "y >= 1" -domain polyhedra

int main() {
    int x, y;
    int a, b, xp, q;

    x = ?;
    // y = __VERIFIER_nondet_int();
    // assume_abort_if_not(y >= 1);

    if (y < 1) {
        return 0;
    }

    a = x;
    b = y;
    xp = 1;
    q = 0;

    int p = 2;
    while (1) {
        // __VERIFIER_assert(q + a * b * p == x * y);

        if (!(a != 0 && b + q + a * b * xp - x * y != 0))
            break;

        if (a % 2 == 0 && b % 2 == 0) {
            a = a / 2;
            b = b / 2;
            xp = 4 * xp;
        } else if (a % 2 == 1 && b % 2 == 0) {
            a = a - 1;
            q = q + b * xp;
        } else if (a % 2 == 0 && b % 2 == 1) {
            b = b - 1;
            q = q + a * xp;
        } else {
            a = a - 1;
            b = b - 1;
            q = q + (a + b + 1) * xp; /*fix a bug here---  was (a+b-1)*/
        }

        p = 1;
    }

    p = a+b;
    // __VERIFIER_assert(q == x * y);
    // __VERIFIER_assert(a * b == 0);
    return 0;
}

// ARGS: -precondition "c == 0 && c < k" -domain polyhedra

int main() {
    int k, x, y, c;

    x = 0;
    y = 0;

    int p;
    p = 0;

    while (c + (y * y) - 2 * x + y < k) {
        p = 1;
        c = c + 1;
        y = y + 1;
        x = y + x;
    }

    p = 0;
}

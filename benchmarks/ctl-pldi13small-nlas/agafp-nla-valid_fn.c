//CTL [AF]([AG](p>0))  
// ARGS: -precondition "c == 0 && c <= k" -domain polyhedra

int main() {
    int k, y, x, c;
    k = ? ;

    y = 0;
    x = 0;
    c = 0;

    int p, xp;
    p = 0;
    xp = ?;

    if (xp > 0) {
        p = p+1;
    }
    else {
        while (c + 4*x - y*y*y*y - 2*y*y*y - y*y < k) {
            c = c + 1;
            y = y + 1;
            x = y * y * y + x;
        }
        p = 1;
  }
    /* while(1) { if(dummy>0) break; } L_return: return 0; */

    return 0;
}

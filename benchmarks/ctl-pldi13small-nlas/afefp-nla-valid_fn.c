//CTL [AF]([EF](p>0)) 
// ARGS: -precondition "c == 0 && c <= k" -domain polyhedra

int main() {
    int X, Y, k;
    int v, xp, y, c;


    X = ?;
    Y = ?;
    k = ?;

    v = 2 * Y - X;
    y = 0;
    xp = 0;
    c = 0;
    
    int p, rho, x;
    p = 0;
    x = 5;
    
    while (2*Y*xp - 2*X*y - X + 2*Y - v + c <= k) {
 
        if (v < 0) {
            v = v + 2 * Y;
        } else {
            v = v + 2 * (Y - X);
            y++;
        }
        xp++;
        c++;
    }
    
    while(1) {
        if(x < 0) break;
        rho = ?;
        if ( rho > 0) {
            x = x - 1;
        }
    }
    p = 1;

    /* while(1) { if(dummy>0) break; } L_return: return 0; */
    
    return 0;
}

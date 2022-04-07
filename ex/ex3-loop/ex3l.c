int term = 0;

int main() {
    int x, y;
    // while( (x<0 && y>0) || (y<0 && x>0) ) {
    while (x * y < 0) {
      x = x + 1;
      y = y + 1;
    }
    term = 1;
    return 0;
}

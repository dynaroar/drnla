#include "../ctl.h"

int x, y;
unsigned int pc;
int __phi() { return CAG( CAP(x >= y) ); }

void init() { x = 1; y = 1; }

int body() {
  while(1) {
    x = x + 1; 
    y = y + 1;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


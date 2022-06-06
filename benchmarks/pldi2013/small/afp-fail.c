#include "../ctl.h"

int y, p;
unsigned int pc;
int __phi() { return CAF( CAP(p > 0) ); }

void init() { p = 0;  }

int body() {
  while(1) {
    if (!(y > 0)) break;
    y = y - 1;
  }
  p = -1;
  while(1) { if(dummy>0) break; } while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


#include "../ctl.h"

// ************************************************************
// EXPECTED RANKING:    x' < x  /\  x > 0
// ************************************************************

int x, p, nd;
unsigned int pc;
int __phi() { return CAF( CAG( CAP(p > 0) ) ); }

void init() { p = 0; }

int body() {
  while(1) {
    if (!(x > 0)) break;
    nd = nondet();
    if (nd > 0) {
      x = x - 1; 
    } else {
      x = x - 2; 
    }
  }
  while(1) {
    nd = nondet();
    if (nd > 0)
      p = 1;
    else 
      p = 2;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


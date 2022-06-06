#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0
//
// EXPECTED RANKING:    y' < y
// ************************************************************

int y, p;
unsigned int pc;
int __phi() { return CAF( CEG( CAP(p <= 0) ) ); }
int __rho_1_;

void init() { p = 0; y = 5; }

int body() {
  __rho_1_ = nondet();
  if(__rho_1_ > 0) {
    while(1) { if(y < 0) { break; } { y = y - 1; } }
    p = 1;
  } else {
    p = 1;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


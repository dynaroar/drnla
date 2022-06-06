#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0
//
// EXPECTED RANKING:    y' < y
// ************************************************************

int y, p, check;
unsigned int pc;
int __phi() { return CAF( CAND(CAP(check == 1), CEG( CAP(p <= 0) ) )); }
int __rho_1_;

void init() { p = 0; y = 5; check = 0; }

int body() {
  check = 1;
  __rho_1_ = nondet();
  if(__rho_1_ > 0) {
    while(1) { if(y < 0) { break; } { check = 1; y = y - 1; } }
    p = 1;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


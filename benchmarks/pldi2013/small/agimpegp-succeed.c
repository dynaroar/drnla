#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0
// ************************************************************

int x, p, check;
unsigned int pc;
int __phi() { return CAG( CIMP(CAP(check == 1), CEG( CAP(p > 0) ) )); }
int __rho_1_;
int __rho_2_;

void init() { p = 1; check = 0; }

int body() {
  while(1) {
    DOCHECK();
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      p = 1;
    } else {
      p = 2;
    }
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


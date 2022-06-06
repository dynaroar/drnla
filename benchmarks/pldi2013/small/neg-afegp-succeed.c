#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0
//
// EXPECTED RANKING:    x' < x  /\  x > 0
// ************************************************************

int x, p, start;
unsigned int pc;
int __phi() { return CEG( CAF( CAP(p <= 0) ) ); }
int __rho_1_;
int __rho_2_;

void init() { p = 0; x = 5; }

int body() {
  while(1) {
    if(x < 0) { break; }
    x = x - 1;
  }
  while(1) {
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      p = 1;
    }
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


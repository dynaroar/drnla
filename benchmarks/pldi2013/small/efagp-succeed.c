#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0     and     __rho_2_ <= 0
//
// EXPECTED RANKING:    x' < x  /\  x > 0
// ************************************************************

int x, p;
unsigned int pc;
int __phi() { return CEF( CAG( CAP(p > 0) ) ); }
int __rho_1_;

void init() { p = 0; x = 5; }

int body() {
  while(1) {
    if(x < 0) break; 
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      x = x - 1;
    }
  }
  p = 1;
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}

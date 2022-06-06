#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0
// ************************************************************

int y, p;
unsigned int pc;
int __phi() { return CAF( CEF( CAP(p <= 0) ) ); }
int __rho_1_;

void init() { p = 1; y = 5; }

int body() {
  __rho_1_ = nondet();
  if(__rho_1_ > 0) {
    p = 1; // 0;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0
// RANKING:             x' < x     y' < y
// ************************************************************

int x, y, p;
unsigned int pc;
int __phi() { return CEF( CAF( CAP(p > 0) ) ); }
int __rho_1_;
int __rho_2_;

void init() { p = 0; x = 5; }

int body() {
  while(1) {
    if ( x < 0 ) break; 
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      x = x - 1;
    } else {
      p = 0;
    }
  }
  while(1) {
    if(y < 0) { break ; } else { y = y - 1; }
  }
  p = 1;
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


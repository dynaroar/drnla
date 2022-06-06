#include "../ctl.h"

// ************************************************************
// EXPECTED RANKING:    y' < y  /\  y > 0
// ************************************************************

int x, y, p, start;
unsigned int pc;
int __phi() { return CEF( CEG( CAP(p <= 0) ) ); }
int __rho_1_;
int __rho_2_;

void init() { p = 0; __rho_1_ = nondet(); x = __rho_1_; }

int body() {
  if(x>0) {
    while (1) { p = p + 1; }
  }
  else {
    while(1) { if (!(y > 0)) break; y = y - 1; }
    p = 0;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


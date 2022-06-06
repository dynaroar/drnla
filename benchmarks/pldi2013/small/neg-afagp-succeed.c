#include "../ctl.h"

// ************************************************************
// EXPECTED RANKING:    x' < x  /\  x > 0
//
// But should fail because AG(p) cannot be established.
// ************************************************************

int x, p, start;
unsigned int pc;
int __phi() { return CEG( CEF( CAP(p <= 0) ) ); }
int __rho_1_;
int __rho_2_;

void init() { p = 0; start = 0; }

int body() {
  start = 1;
  start = 0;
  while(1) { 
    if (!(x > 0)) break;
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      x = x - 1; 
    } else {
      x = x - 2; 
    }
  }

  while(1) {
    __rho_2_ = nondet();
    if (__rho_2_ > 0)
      p = 1;
    else 
      p = 0;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


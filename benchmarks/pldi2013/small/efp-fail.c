#include "../ctl.h"

// ************************************************************
//
// PROPERTY DOES NOT HOLD
//
// ************************************************************

int x;
unsigned int pc;
int __phi() { return CEF( CAP(x > 5) ); }
int __rho_1_;

void init() { x = 0; }

int body() {
  while(1) {
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      x = x - 2; 
    } else {
      x = x - 1; 
    }
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


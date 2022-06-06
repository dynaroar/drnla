#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0     and     __rho_2_ <= 0
//
// EXPECTED RANKING:    x' < x  /\  x > 0
// ************************************************************

int x, p, t;
unsigned int pc;
int __phi() { return CEG( CEF( CAP(p > 0) ) ); }
int __rho_1_;
int __rho_2_;

void init() { p = 0; }

int body() {
  while(1) {
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      while(1) {
	if (! (x > 0)) break; 
	__rho_2_ = nondet();
	if(__rho_2_ <= 0) {
	  x = x - 1;
	} else {
	  t = nondet();
	  assume(t > 0);
	  x = x + t;
	}
      }
      p = 1;
    }
    p = 0;
  }
}

int main() {}

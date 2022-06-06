#include "../ctl.h"

// ************************************************************
// EXPECTED CHUTE:      __rho_1_ > 0     and     __rho_2_ <= 0
//
// EXPECTED RANKING:    x' < x  /\  x > 0
// ************************************************************

int x, p;
unsigned int pc;
int __phi() { return CAG( CAF( CAP(p <= 0) ) ); }
int __rho_1_;
int __rho_2_;

void init() { p = 0; }

int body() {
  while(1) {
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      while(1) {
	if (!(x > 0)) break; 
	__rho_2_ = nondet();
	if(__rho_2_ <= 0) {
	  x = x - 1;
	} else {
	  x = x + 1;
	}
      }
      p = -1;
    }
    p = 0;
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


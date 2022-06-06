#include "../ctl.h"

int x,p;
unsigned int pc;
int __phi() { return CEG( CAP(p > 0) ); }
int __rho_1_;

void init() { x = 5; p = 0; }

int body() {
  while(1) {
    if (!(x > 0)) break;
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      x = x - 1; 
    } else {
      x = x - 2; 
    }
  }
  p = 1;
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


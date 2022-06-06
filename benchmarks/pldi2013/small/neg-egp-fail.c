#include "../ctl.h"

int x;
unsigned int pc;
int __phi() { return CAF( CAP(x <= 1) ); }
int __rho_1_;

void init() { x = 2; }

int body() {
  while(1) {
    __rho_1_ = nondet();
    if (__rho_1_ > 0) {
      x = x + 1; 
    } else {
      x = x - 1; 
    }
  }
  while(1) { if(dummy>0) break; } L_return: return 0;
}

int main() {}


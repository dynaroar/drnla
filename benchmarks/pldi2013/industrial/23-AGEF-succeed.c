int wakend, got_SIGHUP;
void init() { wakend = 1; __rho_1_ = nondet(); got_SIGHUP = __rho_1_; }
int __phi() { return CAG(CEF(CAP(wakend == 1))); }

void body() {
  wakend = 1;
  while(1) {
    if (got_SIGHUP>0) {
      got_SIGHUP = 0;
      __rho_2_ = NONDET;
      if (__rho_2_<=0) break;
    }
    if (wakend>0) { wakend = 0; }
    if (wakend<=0) {
      if (NONDET) wakend = 1;
    }
    __rho_4_ = nondet();
    if (__rho_4 <= 0) { break; }
  }
  while(1) {}
  return 0;
}

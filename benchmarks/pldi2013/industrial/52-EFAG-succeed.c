int wakend, NONDET, got_SIGHUP;
void init() { __rho_2_ = NONDET; wakend = 1; got_SIGHUP = __rho_2_; }
int __phi() { return CEF(CAG(CAP(wakend != 1))); }

void body() {
  wakend = 1;
  while(1) {
    if (got_SIGHUP>0) {
      got_SIGHUP = 0;
      if (__rho_3_<=0) break;
    }
    if (wakend>0) { wakend = 0;__rho_4_ = NONDET; }
    if (wakend<=0) {
      if (__rho_4_ >= 1000) wakend = 1;
    }
    if (__rho_5_<=0) { break; }
  }
  while(1) {}
  return 0;
}

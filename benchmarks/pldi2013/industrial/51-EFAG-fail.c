int wakend, NONDET, got_SIGHUP;
void init() { wakend = 1; got_SIGHUP = nondet(); }
int __phi() { return CEF(CAG(CAP(wakend != 1))); }

void body() {
  wakend = 1;
  while(1) {
    if (got_SIGHUP>0) {
      got_SIGHUP = 0;
      if (NONDET) break;
    }
    if (wakend>0) { wakend = 0; }
    if (wakend<=0) {
      if (NONDET) wakend = 1;
    }
    if (NONDET) { break; } // NONDET issue
  }
  while(1) {}
  return 0;
}


//@ ltl invariant positive: [](AP(x >= 1) ==> <>AP(x == 0));

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int x, n;

int main()
{
  while (1) {
	  x = __VERIFIER_nondet_int();
	  n = __VERIFIER_nondet_int();
	  if (x >= 1) {
	    while (n > 0)
        n--;
      x = 0;
    }		
  }
}

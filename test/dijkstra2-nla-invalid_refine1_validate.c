extern int __VERIFIER_nondet_int(void) ;
int main(void) 
{ 
  int n ;
  int xp ;
  int q ;
  int r ;
  int h ;
  int c ;
  int k ;
  int tmp ;
  int p ;
  int if_too_small_46 ;
  int else_too_big_46 ;
  int else_too_small_46 ;
  int if_too_big_46 ;

  {
  n = __VERIFIER_nondet_int();
  xp = 0;
  q = 1;
  r = n;
  h = 0;
  c = 0;
  tmp = __VERIFIER_nondet_int();
  k = tmp;
  p = 2;
  while (q <= n) {
    q = 4 * q;
  }
  p = 1;

  while (q != 1) {
// adding path condition, so that ultimate can prove it's correct
      if (xp * xp - n * q + q * r == 0){
      /* if (r < 2 * p + q){ */
    if (((xp * xp + r * q) - n * q) + c <= k) {
      if (- c + k <= - 1) {
        else_too_big_46 = 1;
        reach_error();
      } else
      if (! (0 >= c - k)) {
        if_too_small_46 = 1;
        reach_error();
      }
      q /= 4;
      h = xp + q;
      xp /= 2;
      if (r >= h) {
        xp += q;
        r -= h;
      }
      c ++;
    } else {
      if (0 >= c - k) {
        if_too_big_46 = 1;
        reach_error();
      } else
      if (! (- c + k <= - 1)) {
        else_too_small_46 = 1;
        reach_error();
      }
      break;
    }
  }
  }
  p = k + c;
  return (0);
}
}

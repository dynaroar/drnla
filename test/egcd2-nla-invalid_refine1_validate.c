extern int __VERIFIER_nondet_int(void) ;
int main(void) 
{ 
  int x ;
  int y ;
  int a ;
  int b ;
  int xp ;
  int q ;
  int r ;
  int s ;
  int c ;
  int k ;
  int p ;
  int temp ;
  int if_too_small_33 ;
  int else_too_big_33 ;
  int else_too_small_33 ;
  int if_too_big_33 ;

  {
  x = __VERIFIER_nondet_int();
  y = __VERIFIER_nondet_int();
  p = 2;
  if (x < 1) {
    return (x);
  }
  if (y < 1) {
    return (x);
  }
  a = x;
  b = y;
  xp = 1;
  q = 0;
  r = 0;
  s = 1;
  c = 0;
  k = 0;
  while (! (! (b != 0))) {
    c = a;
    k = 0;
    /* if (a == k * b + c){ */
// Strenghten b, ultimate can prove it's correct.
    if (b == 1){
        while (1) {
      if (c >= x * q + y * s) {
        if (- b + c <= - 1) {
          else_too_big_33 = 1;
          reach_error();
        } else
        if (! (0 >= b - c)) {
          if_too_small_33 = 1;
          reach_error();
        }
      } else {
        if (0 >= b - c) {
          if_too_big_33 = 1;
          reach_error();
        } else
        if (! (- b + c <= - 1)) {
          else_too_small_33 = 1;
          reach_error();
        }
        break;
      }
      c -= b;
      k ++;
    }
    }
    p = 1;
    a = b;
    b = c;
    temp = xp;
    xp = q;
    q = temp - q * k;
    temp = r;
    r = s;
    s = temp - s * k;
  }
  p = (c - b) + 1;
  return (a);
}
}

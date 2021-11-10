#include <stdio.h>
#include <stdlib.h>

void vtrace10(int x, int y, int atomic0) {}
void vtrace11(int x, int y, int atomic0) {}
void vtrace13(int x, int y, int atomic0) {}
void vtrace15(int x, int y, int a, int atomic0) {}
int mainQ(int i ) 
{ 
  int x=0;
  int y =0;
  int a = 0;
  int atomic0 =0 ;
  while (a<20) {
    x = 1;
    atomic0 = y == 0;
   // vtrace10(x, y, _atomic0);
    y = 1;
    atomic0 = y == 0;
   // vtrace11(x, y, _atomic0);
    while (x > 0) {
      x --;
      atomic0 = y == 0;
   //   vtrace13(x, y, atomic0);
      y = 0;
      atomic0 = y == 0;
      vtrace15(x, y, a, atomic0);
    }
    a++;
  }
 return y;
}
void main(int argc , char **argv ) 
{ 

    mainQ(atoi(argv[1]));
}

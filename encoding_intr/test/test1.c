#include <stdio.h>
#include <stdlib.h>
// F(y=0)

void vtrace(int x, int y) {}
int mainQ(int i) {
   int x=0; int y=0; // vtrace1(x,y);
   int a=0;
   x=i;
   y=2;
   a = 0;
    while(a<10) {
      x = 1;   //vtrace2(x,y);
      y=1;     //vtrace3(x,y);
      while(x>0) {
          x--;
       //vtrace5(x,y);
   }
   y = 0;
   /* vtrace(x, y); */
    a++;
}
return y;
}

void main(int argc, char **argv) {
    //mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
    mainQ(atoi(argv[1]));
}

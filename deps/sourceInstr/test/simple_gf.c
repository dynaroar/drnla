// G(x=1 => F(x=0))
//G(x!=1 \/ F(x=0))

#include<stdio.h>
#include<stdlib.h>
void vassume(int b){}
/* void vtrace1(int x, int c, int c2, int r, int c1){} */
/* void vtrace2(int x, int c, int c2, int r, int c1){} */
void vtrace1(int _xeq1, int _xeq0){}
void vtrace2(int _xeq1, int _xeq0){}
/* void vtrace3(int _xeq1, int _xeq0){} */
/* void vtrace4(int _xeq1, int _xeq0){} */

// int mainQ(int c, int n) {
int mainQ(int c, int n) {
    vassume(c >= 0);
    //if(c < 0) return 0;
    int c2=c;
    int x, r=0;
    int j1 = 0;
    int _xeq1 = 0;
    int _xeq0 = 0;
    while(j1 <= 50) {
        j1++;
        int c1=c;
        while(c1>0) {
          r = r+c1; 
          c1--;   }
          x = (2*r) - (c*c) -c + 1;  _xeq1 = (x == 1); _xeq0 = (x == 0);
          vtrace1(_xeq1, _xeq0);  
        // DIG Infer:  { x == 1 }
        while(n>0) n--; 
        r=0;  
        while(c2>0) {
          r = r+c2;
          c2--;
         }
        x =  (2*r) - (c*c)-c;   _xeq1 = (x == 1); _xeq0 = (x == 0);    // DIG Infer: { x = 0; }
        vtrace2(_xeq1, _xeq0);
    }
}

void main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}


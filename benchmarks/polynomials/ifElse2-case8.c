#include <stdio.h>
#include <stdlib.h>

/* void __VERIFIER_error() {} */
void reach_error() {}
void __VERIFIER_assert(int cond) {}
void __VERIFIER_assume(int cond) {}
void vassert(int cond) {}

int __VERIFIER_nondet_int() {}
void vtrace1(int x, int tmp1, int y){}
void vtrace2(int x, int tmp1, int y){}
void vtrace3(int x, int tmp1, int y){}

int x;

int main(){
    x = __VERIFIER_nondet_int();
     /* vtrace1(x, tmp1, y); */
    /* if (x*x-1 >= 0) */
    if (x*x -100 > 0 && x >= 11 && 0<=x && x<=10)
    {
        reach_error();
    } else if (x*x -100 > 0 && x >= 11 && !(0<=x && x<=10)){
        return 1;
    } else if (x*x -100 > 0 && !(x >= 11) && (0<=x && x<=10)){
        reach_error();
    } else if (x*x -100 > 0 && !(x >= 11) && !(0<=x && x<=10)){
        if (x == -11 || x == -12 || x == -13) return 1;
        reach_error();
    } else if (!(x*x -100 > 0) && (x >= 11) && (0<=x && x<=10)){
        reach_error();
    } else if (!(x*x -100 > 0) && (x >= 11) && !(0<=x && x<=10)){
        reach_error();
    } else if (!(x*x -100 > 0) && !(x >= 11) && (0<=x && x<=10)){
        return 1;
    } else if (!(x*x -100 > 0) && !(x >= 11) && !(0<=x && x<=10)){
        reach_error();
 } else {
        return 1;
    }    
     
 }

/* void main(int argc, char **argv){ */
/*     mainQ(atoi(argv[1]), atoi(argv[2])); */
/* } */

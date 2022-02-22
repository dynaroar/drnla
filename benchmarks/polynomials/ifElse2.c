#include <stdio.h>
#include <stdlib.h>

void __VERIFIER_error() {}
void __VERIFIER_assert(int cond) {}
void __VERIFIER_assume(int cond) {}
void vassert(int cond) {}

int __VERIFIER_nondet_int() {}
void vtrace1(int x){}
void vtrace2(int x){}
void vtrace3(int x){}

int x, y;

int mainQ(int x){
    /* int tmp1; */
    /* tmp1 = x*x-100; */
    /* vtrace1(x, tmp1); */
    if (x*x-100 > 0){
    /* if (tmp1 > 0){ */
        vtrace2(x);
        return 0;
    }  else {
        vtrace3(x);
        /* vassert(-10 <= x <=10); */
        vassert(-10 <= x <=10);
    }
}

void main(int argc, char **argv){
    /* mainQ(atoi(argv[1]), atoi(argv[2])); */
    mainQ(atoi(argv[1]));
}

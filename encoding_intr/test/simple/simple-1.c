//#Safe
//@ ltl invariant positive: (<> AP(x > 10000));
//@ ltl invariant positive: (<> AP(x > 50));

/* int x=0; */

#include "stdio.h"
#include "stdlib.h"
#include "assert.h"
#include "math.h"

void vtrace1(int x, int z, int atomic0){}
void vtrace2(int x, int z, int atomic0){}
/* void vtrace1(int x, int z){} */
/* void vtrace2(int x, int z){} */

void mainQ(int a)
{

    int x=0;
    int z=0;
    int atomic0;
    atomic0 = x>50 ;
    /* while(1){ */
    vtrace1(x, z, atomic0);
    /* vtrace1(x, z); */
    while(z<10){
        if(x<5){
            x++;
        } else {
            /* x = nla/bitwise; */
            /* x = (z|x)*x; */
            x = x*6;
        }
        x++;
        z++;
    }
    x=x+1;
    atomic0 = x>50;
    vtrace2(x, z, atomic0);
    /* vtrace2(x, z); */
}

void main(int argc, char **argv) {
    //mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
    mainQ(atoi(argv[1]));
}

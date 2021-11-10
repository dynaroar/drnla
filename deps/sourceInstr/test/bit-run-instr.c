#include <stdio.h>
#include <stdlib.h>

int mainQ(int a , int b )
{
    int c ; int x; int y; /* INSTRUMENTATION: */ int pre_x; 
    x = a;
    y = b;
    int d;
    {
        c = 0;
        // vtrace20(x, y, c, d, pre_x);
        /* x = __VERIFIER_nondet_int(); */
        /* // vtrace21(x, y, c, d, pre_x); */
        /* y = __VERIFIER_nondet_int(); */
        /* // vtrace22(x, y, c, d, pre_x); */
        while (c <= 50) {
            c ++;
            d = rand() % 5000;
            if (d<0) d = d * (-1);
            // vtrace24(x, y, c, d, pre_x);
            x = rand() % 5000;
            y = 1;
            // vtrace25(x, y, c, d, pre_x);
            printf("vtrace25; %i; %i; %i; %i; %i\n", x, y, c, d, pre_x);
            while (x > 0) {
                d--;
                // vtrace27(x, y, c, d, pre_x);
                /* x &= c - 1; */
                /* INSTRUMENTATION: */ pre_x = x; 
                x = (x & d) - 1;
                // vtrace28(x, y, c, d, pre_x);
                printf("vtrace28; %i; %i; %i; %i; %i\n", x, y, c, d, pre_x);
                if (x <= 1) {
                    y = 0;
                    // vtrace30(x, y, c, d, pre_x);
                    printf("vtrace30; %i; %i; %i; %i; %i\n", x, y, c, d, pre_x);
                }
            }
        }
        return (0);
    }
}

int main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

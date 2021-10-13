#include <stdio.h>
#include <stdlib.h>

int mainQ(int a , int b )
{
    int c ; int x; int y;
    x = a;
    y = b;
    int d;
    {
        c = 0;
        // vtrace20(x, y, c, d);
        /* x = __VERIFIER_nondet_int(); */
        /* // vtrace21(x, y, c, d); */
        /* y = __VERIFIER_nondet_int(); */
        /* // vtrace22(x, y, c, d); */
        while (c <= 50) {
            c ++;
            d = rand() % 5000;
            if (d<0) d = d * (-1);
            // vtrace24(x, y, c, d);
            x = rand() % 5000;
            y = 1;
            // vtrace25(x, y, c, d);
            printf("vtrace25; %i; %i; %i; %i\n", x, y, c, d);
            while (x > 0) {
                d--;
                // vtrace27(x, y, c, d);
                /* x &= c - 1; */
                x = (x & d) - 1;
                // vtrace28(x, y, c, d);
                printf("vtrace28; %i; %i; %i; %i\n", x, y, c, d);
                if (x <= 1) {
                    y = 0;
                    // vtrace30(x, y, c, d);
                    printf("vtrace30; %i; %i; %i; %i\n", x, y, c, d);
                }
            }
        }
        return (0);
    }
}

int main(int argc, char **argv){
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

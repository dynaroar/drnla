#include <stdio.h>
#include <stdlib.h>
// F(y=0)
void vassume(int b){}

void vtrace1(int x, int y, int atomic0){};
void vtrace2(int x, int y, int atomic0){};

/* void vtrace(int x, int y) {} */
int mainQ(int x, int y) {
    int atomic0 = 0;
    vassume(x>y);
    vassume(y>0);
    atomic0= y== 0;
    vtrace1(x, y, atomic0);

    while (x>0){
        x--;
        y--;
    }
    atomic0= y== 0;
    vtrace2(x, y, atomic0);

return y;
}

void main(int argc, char **argv) {
    //mainQ(atoi(argv[1]), atoi(argv[2]), atoi(argv[3]));
    mainQ(atoi(argv[1]), atoi(argv[2]));
}

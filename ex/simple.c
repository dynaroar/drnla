#include <stdlib.h>


// G(x=1 => F(x=0))

int original() {
    int x, n;
    while(1) {
        x = (c*c - (c*c) + 1); // DIG Infer:  { x == 1 }
        n = random();
        while(n>0) n --;  // TODO make this NLA
        x = (d*d - d*d);       // DIG Infer: { x = 0; }
    }
}

int step1() {
    int x, n;
    while(1) {
        x = (c*c - (c*c) + 1); _xeq1 = (x == 1); _xeq0 = (x == 0);
        n = random();          _xeq1 = (x == 1); _xeq0 = (x == 0);
        while(n>0) { n --;     _xeq1 = (x == 1); _xeq0 = (x == 0); }
        x = (d*d - d*d);       _xeq1 = (x == 1); _xeq0 = (x == 0);
    }
}

int step2() {
    int x, n;
    while(1) {
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;
        n = random();          _xeq1 = true; _xeq0 = false;
        while(n>0) n --;       _xeq1 = true; _xeq0 = false;
        x = (d*d - d*d);       _xeq1 = false; _xeq0 = true;
    }
}

// G(x=1 => F(x=0))
// Now find all locations from which this terminates: F(x=0)
int step3() {
    int x, n;
    while(1) {
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;
        n = random();
        if (x == 0) { while (1) {}; } 
        while(n>0) n --;  
        x = (d*d - d*d);     exit(); // _xeq1 = false; _xeq0 = true;
    }
}

// result: F(x=0)
int step4() {
    int x, n;                                                _F_xeq0 = true;
    while(1) {                                               _F_xeq0 = true;
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;  _F_xeq0 = true;
        n = random();                                        _F_xeq0 = true;
        while(n>0) n --;                                     _F_xeq0 = true;
        x = (d*d - d*d);      _xeq1 = false; _xeq0 = true;   _F_xeq0 = true;
    }
}

// x=1 => F(x=0)
// construct !xeq1 VEE _F_xeq0
int step5() {
    int x, n;                                                _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true;
    while(1) {                                               _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true;
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;  _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true;
        n = random();                                        _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true;
        while(n>0) n --;                                     _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true;
        x = (d*d - d*d);      _xeq1 = false; _xeq0 = true;   _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true;
    }
}

// G(x=1 => F(x=0))
// Prove G by replacing _OR with error();
int step6() {
    int x, n;                                                _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true; if(!_OR_NOT_xeq1_Fxeq0) error();
    while(1) {                                               _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true; if(!_OR_NOT_xeq1_Fxeq0) error();
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;  _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true; if(!_OR_NOT_xeq1_Fxeq0) error();
        n = random();                                        _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true; if(!_OR_NOT_xeq1_Fxeq0) error();
        while(n>0) { n --;                                   _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true; if(!_OR_NOT_xeq1_Fxeq0) error(); }
        x = (d*d - d*d);      _xeq1 = false; _xeq0 = true;   _F_xeq0 = true; _OR_NOT_xeq1_Fxeq0 = true; if(!_OR_NOT_xeq1_Fxeq0) error();
    }
}


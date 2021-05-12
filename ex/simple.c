#include <stdlib.h>

int original() {
    int x, n;
    while(1) {
        x = (c*c - (c*c) + 1); // DIG Infer:  { x == 1 }
        n = random();
        while(n>0) n --;  // TODO make this NLA
        x = (d*d - d*d);       // DIG Infer: { x = 0; }
    }
}

int step2() {
    int x, n;
    while(1) {
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;
        n = random();
        while(n>0) n --;  
        x = (d*d - d*d);      _xeq1 = false; _xeq0 = true;
    }
}

// Now find all locations from which this terminates:
int step3() {
    int x, n;
    while(1) {
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;
        n = random();
        while(n>0) n --;  
        x = (d*d - d*d);     exit(); // _xeq1 = false; _xeq0 = true;
    }
}

// result:
int step4() {
    int x, n;                                                _F_xeq0 = true;
    while(1) {                                               _F_xeq0 = true;
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;  _F_xeq0 = true;
        n = random();                                        _F_xeq0 = true;
        while(n>0) n --;                                     _F_xeq0 = true;
        x = (d*d - d*d);      _xeq1 = false; _xeq0 = true;   _F_xeq0 = true;
    }
}


// construct xeq0 VEE _F_xeq0
int step5() {
    int x, n;                                                _F_xeq0 = true; _OR_xeq0_Fxeq0 = true;
    while(1) {                                               _F_xeq0 = true; _OR_xeq0_Fxeq0 = true;
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;  _F_xeq0 = true; _OR_xeq0_Fxeq0 = true;
        n = random();                                        _F_xeq0 = true; _OR_xeq0_Fxeq0 = true;
        while(n>0) n --;                                     _F_xeq0 = true; _OR_xeq0_Fxeq0 = true;
        x = (d*d - d*d);      _xeq1 = false; _xeq0 = true;   _F_xeq0 = true; _OR_xeq0_Fxeq0 = true;
    }
}


// Prove G by replacing _OR with error();
int step5() {
    int x, n;                                                _F_xeq0 = true; _OR_xeq0_Fxeq0 = true; if(!_OR_xeq0_Fxeq0) error();
    while(1) {                                               _F_xeq0 = true; _OR_xeq0_Fxeq0 = true; if(!_OR_xeq0_Fxeq0) error();
        x = (c*c - (c*c) + 1); _xeq1 = true; _xeq0 = false;  _F_xeq0 = true; _OR_xeq0_Fxeq0 = true; if(!_OR_xeq0_Fxeq0) error();
        n = random();                                        _F_xeq0 = true; _OR_xeq0_Fxeq0 = true; if(!_OR_xeq0_Fxeq0) error();
        while(n>0) n --;                                     _F_xeq0 = true; _OR_xeq0_Fxeq0 = true; if(!_OR_xeq0_Fxeq0) error();
        x = (d*d - d*d);      _xeq1 = false; _xeq0 = true;   _F_xeq0 = true; _OR_xeq0_Fxeq0 = true; if(!_OR_xeq0_Fxeq0) error();
    }
}


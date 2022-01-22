//@ ltl invariant positive: [](<>AP(y == 1));

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));

int x, y, z;
int main(){
    y = 0;

    while(1){
        z = __VERIFIER_nondet_int();
        x = -(z-1)*(z-1)+7;
        if(x<=7){
            y=1;
        }
    }
}

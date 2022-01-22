// https://github.com/ultimate-pa/ultimate/blob/dev/trunk/examples/LTL/koskinen/dpredicates-benchmarks/win6.c

//@ ltl invariant positive: <>([]AP(WItemsNum >= 1));

extern void __VERIFIER_error() __attribute__ ((__noreturn__));
extern void __VERIFIER_assume() __attribute__ ((__noreturn__));
extern int __VERIFIER_nondet_int() __attribute__ ((__noreturn__));


void callback1() {}
void callback2() {}

int WItemsNum, MoreWItems;
/* int MoreItems() { */
/*     int i = __VERIFIER_nondet_int(); */
/*     return i; */
/* } */

int main() {
    WItemsNum = __VERIFIER_nondet_int();
    while(1) {
        MoreWItems = __VERIFIER_nondet_int();
        while(WItemsNum <= 5 || MoreWItems) {
            if (WItemsNum<=5) {
                callback1();
                WItemsNum++;
                
            } else {
                WItemsNum++;
            }
        }
    
        while(WItemsNum * WItemsNum > 4) {
            callback2();
            WItemsNum--;
        }
    }
    while(1) {}
}


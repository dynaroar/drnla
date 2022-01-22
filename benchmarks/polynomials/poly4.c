//https://github.com/ultimate-pa/ultimate/blob/dev/trunk/examples/LTL/simple/cav2015.c

//@ ltl invariant positive: [](AP(z > 1) ==> <>AP(y == 0));

extern int __VERIFIER_nondet_int();

int x,y,z;

int main(){
    while(1){
        x = __VERIFIER_nondet_int();
        y = 1;
        z = x * x + 1;
        while(z-1>0){
            x--;
            if(x<=1){
                y=0;
            }
        }
    }
}

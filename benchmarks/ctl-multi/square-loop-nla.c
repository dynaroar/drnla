extern int __VERIFIER_nondet_int(void);
int main() {
    int x, y;
    x = __VERIFIER_nondet_int();
    y = __VERIFIER_nondet_int();
    while (y>0){
        if (x*x>49) y = y-5;
        y--;
    }
    return x;
}

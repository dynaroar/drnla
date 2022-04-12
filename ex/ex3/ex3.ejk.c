// invariant positive: <>(AP(fail == 1) && AP(agree_sign == 0));

//@ ltl invariant positive: [](AP(agree_sign == 1) ==> <>(AP(fail == 2)));

// invariant positive: <>(AP(fail == 1)) || <>(AP(fail == 2));
// invariant positive: <>(AP(fail != 0));
//[](AP(set != 0) ==> <> AP(unset!= 0));

int fail;
int agree_sign = 0;
int main() {
    int x = __VERIFIER_nondet_int();
    int y = __VERIFIER_nondet_int();
    __VERIFIER_assume(x != 0 && y != 0);
    agree_sign = (x >= 0 && y >= 0 ? 1 : (x < 0 && y < 0 ? 1 : 0 ));
    fail = 0;
    if (x * y < 0) {
        fail = 1;
        return 1;
    } else {
	fail = 2;
        return 0;
    }
}

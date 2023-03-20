#!/bin/sh

printHelp(){
    echo "-h:     Help"
    echo "-b:     Specify benchmark directory."
    echo "-d:     Delete output directory."
}

BASHDIR=$(dirname $0)

while getopts "hb:d" arg
do
    case $arg in
        h)
            printHelp ;;
        b)
            BENDIR=$OPTARG ;;
        d)
            CLEAR=1 ;;
        :)
            echo "Error: -${OPTARG} requires an argument." exit_abnormal ;;
    esac
done

#if [[$OUTPUT == " "]]; then
#    OUTPUT="$BENDIR/Output"
#fi
OUTPUT="$BENDIR/Output"
if [ ! -d $OUTPUT ]
then
    mkdir $OUTPUT
fi

# echo $OUTPUT
cp $BENDIR/*.c $OUTPUT
programs=$(ls $OUTPUT/*.c)
for src in $programs;do
    sed -i '1 i\#include <stdlib.h>' $src
    sed -i 's/extern int __VERIFIER_nondet_int(.*).*/int __VERIFIER_nondet_int(){return rand();}/' $src
    sed -i 's/int main(.*).* {/int main(){int lbnd = 0; while (lbnd<5) {lbnd++;/' $src
    sed -i 's/return.*0.*;/} return 0;/' $src
done

echo "compiling..."
for src in $programs;do
    name="${src%.*}"
    bin="${name}_bin"
    gcc $src -o $bin
done
echo "---Done"

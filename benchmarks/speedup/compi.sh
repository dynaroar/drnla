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
OUTPUT="$BENDIR/output"
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
    # sed -i 's/int main(.*).*{/int main(){int lbnd = 0; while (lbnd<5) {lbnd++;/' $src
    sed -i 's/int main(.*)/int main(int argc, char *argv[])/' $src
    # sed -i 's/^{/{int lbnd = 0; while (lbnd<5) {lbnd++;/' $src
    # sed -i 's/return.*0.*;/} return 0;/' $src
done

echo "compiling and run..."

table="$OUTPUT/runtime.tex"
if [ -e $table ]; then
    echo "File $table already exists! Will be overwritten"
    rm $table
    echo "Benchmark & Origin & Linear & Speedup" >> $table
else
    echo "Benchmark & Origin & Linear & Speedup" >> $table
fi
    
for src in $programs;do
    bench_name=$(basename $src .c)
    name="${src%.*}"
    bin="${name}_bin"
    gcc $src -o $bin

    # echo "----running $bench_name..."
    # # bin_time=$({ time ./$bin >/dev/null; } 2>&1 | grep real)
    # { time ./$bin >/dev/null; } 2>&1 | grep real
    echo "$bench_name & $runtime & - & -" >> $table 
done
echo "---Done"

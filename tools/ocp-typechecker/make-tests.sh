for f in tests/*.ml; do
    FILE=$(basename $f);
    FNAME=${FILE%.*};
    OUTPUT=$(dirname $f)/$FNAME.output;
    RES=$(dirname $f)/$FNAME.res;
    ARGFILE=$(dirname $f)/$FNAME.args;

    ## Reads args from <file>.args to use to type the program
    ARGS="";
    if [ -f $ARGFILE ]; then
        ARGS=$(cat $ARGFILE);
    fi

    ## Generates output file if it does not exist
    if [ ! -f $OUTPUT ]; then
       echo "(* $f *)" > $OUTPUT;
       ocamlc -i $ARGS $f >> $OUTPUT;
    fi

    printf "Testing \e[1m$f\e[0m: ";
    ./typecheck.asm -I $(ocamlc -where) $f $ARGS > $RES;

    DIFF=$(dirname $f)/$FNAME.diff;
    if diff -d $OUTPUT $RES > /dev/null; then
        echo -e "\e[1m\e[0;32mOK\e[0m";
    else
        echo -e "\e[1m\e[0;31mFailed\e[0m";
        diff $OUTPUT $RES > $DIFF;
    fi
done

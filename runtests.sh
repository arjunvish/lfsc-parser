#!/bin/sh
if [[ -f main.native ]]; then
    if [[ -f translation.lean ]]; then
        rm translation.lean;
    fi
    touch translation.lean
    echo "import sigs.th_base" >> translation.lean
    echo "open smt" >> translation.lean
    echo "open th_base" >> translation.lean
    echo "" >> translation.lean
    for i in $(find ./tests -name "*.plf"); do
      echo -e "/-$i-/" >> translation.lean
      echo $i
      ./main.native $i >> translation.lean
      echo -e "\n" >> translation.lean
    done
    echo "$(lean translation.lean | grep error | wc -l) errors"
    echo "Try 'lean translation.lean' for more detail"
else
    echo "Run 'make' first"
fi

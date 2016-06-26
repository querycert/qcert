#!/bin/bash

declare -a WHITELIST=(".vo" ".glob" ".v.d" ".aux")

for FILE in "$@"
do
    for ending in "${WHITELIST[@]}"
    do
	BASE=${FILE%%${ending}}
	if [[ "$FILE" == "$BASE$ending" ]]
	then
	    COQFILE=${BASE}.v
	    if [ ! -f "${COQFILE}" ]
	    then echo "deleting detritus $FILE"
		 rm -f "${FILE}"
	    fi
	fi
    done
done     

#!/bin/bash

declare -a WHITELIST=(".glob")

for FILE in "$@"
do
    for ending in "${WHITELIST[@]}"
    do
	BASE=${FILE%%${ending}}
	if [[ "$FILE" == "$BASE$ending" ]]
	then
	    echo "copying glob $FILE"
	    cp "${FILE}" docs/globs
	fi
    done
done     

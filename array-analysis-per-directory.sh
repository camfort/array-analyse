#!/bin/sh
for dir in ./*/
do
    dir=${dir%*/}
    dir=${dir##*/}
    array-analysis $dir &
done

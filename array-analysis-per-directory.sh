#!/bin/sh
for dir in ./*/
do
    dir=${dir%*/}
    dir=${dir##*/}
    array-analysis $dir &
    args="$(echo $args $dir)"
done
array-analysis COMBINE $args

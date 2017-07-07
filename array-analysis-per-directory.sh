#!/bin/sh
for dir in ./*/
do
    dir=${dir%*/}
    dir=${dir##*/}
    if [ $# -eq 0 ]
     then
       array-analysis $dir
    elif [ $1 = "par" ]
      then
       echo "Spawning off analysis in parallel version"
       array-analysis $dir &
    fi
    args="$(echo $args $dir)"
done
array-analysis COMBINE $args

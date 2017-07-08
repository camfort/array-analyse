#!/bin/sh
find . -iname "*.f*" -exec sh -c "echo '{}'; array-analysis SINGLE $1 '{}' 2>&1 1>$1.debug" \;

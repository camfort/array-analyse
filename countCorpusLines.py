#!/usr/bin/python

import sys
import subprocess
import os
import re

corpus = sys.argv[1]

def sanitize(s):
    s = s.strip()
    s = re.sub("[_-]","",s)
    for (i,j)  in enumerate(["zero","one","two","three","four","five","six","seven","eight","nine","ten"]):
        s = re.sub("%d" % i,j,s)
    return s

(overallFiles, overallLoC) = (0,0)
for package in ["blas","computational-physics-2","e3mg-ea","geos-chem","hybrid4","navier","um"]:
    if os.path.isdir(corpus+"/"+package):
        count = subprocess.check_output(["bash","-c","find -L %s \( -iname \"*.f\" -o -iname \"*.f90\" \) -exec echo '\"{}\"' \; | xargs cloc --quiet --csv 2>/dev/null | grep -vE \"Counting|files,language\"" % (corpus+"/"+package)])
        (totalFiles,totalLoC) = (0,0)
        for line in count.split("\n"):
            if line.strip():
                (files,lang,blank,comment,loc) = line.strip().split(",")
                totalFiles += int(files)
                totalLoC += int(loc)
        cmd = sanitize(package)
        print "\\newcommand{\\%sFiles}{%s}" % (cmd,totalFiles)
        print "\\newcommand{\\%sLoC}{%s}" % (cmd,totalLoC)
        overallFiles += totalFiles
        overallLoC += totalLoC

print "\\newcommand{\\overallFiles}{%s}" % (overallFiles)
print "\\newcommand{\\overallLoC}{%s}" % (overallLoC)


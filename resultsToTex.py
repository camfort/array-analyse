#!/usr/bin/python

import sys
import re

def sanitize(s):
    s = s.strip()
    s = re.sub("_","",s)
    for (i,j)  in enumerate(["zero","one","two","three","four","five","six","seven","eight","nine","ten"]):
        s = re.sub("%d" % i,j,s)
    return s

with open(sys.argv[1]) as f:
    for l in f:
        if l.strip():
            if l[0:7] == "overall":
                corpus = "overall"
            elif l[0:6] == "corpus":
                corpus = l.split(":")[1].strip()
            else:
                (key,value) = map(lambda x:x.strip(),l.split(":"))
                print "\\newcommand{\\%s}{%s}" % (sanitize(corpus+key),value)

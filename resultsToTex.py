#!/usr/bin/python

import sys
import re
from collections import defaultdict

def sanitize(s):
    s = s.strip()
    s = re.sub("_","",s)
    for (i,j)  in enumerate(["zero","one","two","three","four","five","six","seven","eight","nine","ten"]):
        s = re.sub("%d" % i,j,s)
    return s

files = {}

with open(sys.argv[2]) as f:
    for l in f:
        (k,v) = re.match("\\\\newcommand{\\\\(.*)}{(.*)}",l.strip()).groups()
        files[k] = v

corpora = defaultdict(lambda:{})
keys = {}
with open(sys.argv[1]) as f:
    for l in f:
        if l.strip():
            if l[0:7] == "overall":
                corpus = "overall"
            elif l[0:6] == "corpus":
                corpus = sanitize(l.split(":")[1])
            else:
                (key,value) = map(lambda x:x.strip(),l.split(":"))
                key = sanitize(key);
                keys[key] = 1
                corpora[corpus][key] = 1
                print "\\newcommand{\\%s}{%s}" % (corpus+key,value)
                files[sanitize(corpus+key)] = value

(totalTickAssign, totalTickAssignSuccess, totalLoC) = (0,0,0)
for corpus in corpora.keys():
    if corpus != "overall" and corpus != "ethreemgmodernise":
        for key in keys.keys():
            if not corpora[corpus].has_key(key):
                print "\\newcommand{\\%s}{0}" % (corpus+key)
        loc = files[corpus+"LoC"]
        tickAssign = files[corpus+"tickAssign"]
        tickAssignSuccess = files[corpus+"tickAssignSuccess"]
        totalTickAssign += int(tickAssign)
        totalTickAssignSuccess += int(tickAssignSuccess)
        totalLoC += int(loc)
        print "\\newcommand{\\%s}{%.2g}" % (corpus+"tickAssignPercent", float(tickAssign) / float(loc) * 100)
        print "\\newcommand{\\%s}{%.2g}" % (corpus+"tickAssignSuccessPercent", float(tickAssignSuccess) / float(loc) * 100)

print "\\newcommand{\\%s}{%.2g}" % ("overalltickAssignPercent", float(totalTickAssign) / float(totalLoC) * 100)
print "\\newcommand{\\%s}{%.2g}" % ("overalltickAssignSuccessPercent", float(totalTickAssignSuccess) / float(totalLoC) * 100)


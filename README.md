# array-analyse

Provides a tool for analyising array programming idioms in Fortran
code, based on the CamFort static analysis tools.

# Installation

There are two binaries built by this project:
  * `array-analysis` which performs the static analysis and classification of arrays, generating a data file
  * `study` which takes a data file and performs some more coarse grained classification on the data

You can intall these via `stack`, e.g.,

    stack install

or cabal

    cabal configure
    cabal build
    cabal install

# Usage

Usage:
    
    array-analysis [MODE] [OPTIONS] dir-or-file [excluded-files]

Options: -b 	 print pattern bins
         -d 	 debug mode

Modes:
  Restart the analysis with the intermediate file rfile.restart:
    
     array-analysis RESTART rfile [OPTIONS] dir-or-file [excluded-files]

 Apply the analysis to a single file with restart file rfile.restart:
    
     array-analysis SINGLE rfile [OPTIONS] dir-or-file [excluded-files]

 Restart the analysis with rfile.restart and suppress the final result file 
    
     array-analysis VIEW rfile

 Perform sloccount on the files contributing to rfile.restart
    
     array-analysis SLOC rfile

 Show just the file names contributed to the restart file rfile.restart
    
     array-analysis DIRS rfile

 Combine restart files
 
     array-analysis COMBINE rfile1 rfile2...rfilen

 Compare two restart files
   
     array-analysis CMP rfile1 rfile2

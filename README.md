plb.py generates initial DSLUT code point allocation
Running example:
InInput=6 # DSLUT inputs
LibFileName="./dsdlib/dsdlibDump/lib_all. txt" # Objective Library
Dslut_deeker=DSLUT_Seeker (InInput, libFileName) # DSLUT initial bit assignment generation
seekDslut. py performs Bayesian optimization on initial bit assignments
Running example:
genSpaceFromInitAddBit(nInputs, nBits, bitAssign, pos, num)
#Initial number of SRAM for nBits DSLUT
#pos   the location of the new SRAM
#num   new SRAM index
plb.py performs Boolean matching to obtain function coverage
Running example:
dslut_seeker.exportMatchResult()

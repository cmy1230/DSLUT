import time
import os
import platform
import operator

import hyperopt as hp
from hyperopt.mongoexp import MongoTrials
import plb

curOs = platform.system()
#print("Current OS: ", curOs)
if curOs == "Linux":
    flagLinux = True
elif curOs == "Windows":
    flagLinux = False
else:
    print("Unknown system")
    exit()

def canonicalizeBitAssign(bitAssign):
    nBits = max(bitAssign)
    lenba = len(bitAssign)
    bitToPos = [ [] for x in range(nBits+1) ]

    for pos in range(lenba):
        bit = bitAssign[pos]
        bitToPos[bit].append(pos)

    '''
    print("bitToPos")
    for item in bitToPos:
        print(item)
    '''

    resBitAssign = [-1 for x in range(lenba)]
    index = 1
    for pos in range(len(bitAssign)):
        if resBitAssign[pos] != -1:
            continue
        if bitAssign[pos] == 0:
            resBitAssign[pos] = 0
            continue
        bit = bitAssign[pos]
        for bitPos in bitToPos[bit]:
            resBitAssign[bitPos] = index
        index += 1

    #print(resBitAssign)
    return resBitAssign



class DslutObjective(object):
    def __init__(self, nInputs, libFileName, mongoInfo=None, expKey=None):
        if mongoInfo:
            self.mongoInfo = mongoInfo
            if expKey:
                self.expKey = expKey
            else:
                exit("ExpKey is missing")
        else:
            self.mongoInfo = None
        self.nInputs = nInputs
        self.libFileName = libFileName
        self.nProcs = 8
        self.chunkSize = 1
        self.maxConflicts = 100000
        self.seeker = plb.DSLUT_Seeker(nInputs, libFileName)
        self.targetFuncList = [func for func in self.seeker.funcList if func.nSupp <= self.nInputs]
        self.pd = plb.PlbDescription(plb.PlbType.SINGLE_DSLUT)
        self.nBitsLut = 2**self.nInputs
        self.pd.isCompList = [ False for i in range(self.nBitsLut) ]
    
    def __call__(self, args):
        if len(args) > self.nBitsLut:
            exit("Error in DslutObjective.call(): Invalid input: args")

        numIdenticalTrialLimit = 1
        bitAssignBuf = []
        for item in args:
            bitAssignBuf.append(int(item)) #For type convertion 
        self.pd.bitAssign = canonicalizeBitAssign(bitAssignBuf)
        
        if self.mongoInfo:
            trials = MongoTrials(self.mongoInfo, exp_key=self.expKey)
            cnt = 0
            for item in trials.results:
                if item['status'] == hp.STATUS_OK:
                    if operator.eq(self.pd.bitAssign, item['bitAssign']):
                        cnt += 1
            if cnt >= numIdenticalTrialLimit:
                return { 'status': hp.STATUS_FAIL }

            
        self.pd.nBits = max(self.pd.bitAssign)

        result = self.seeker.match(self.nInputs, self.pd, self.targetFuncList, 
                          self.nProcs, self.chunkSize, self.maxConflicts)
        coverage, numFuncCovered, numFunc = result

        resMap = dict()
        if self.mongoInfo:
            resMap['numPrev'] = len(trials)
        resMap['coverage'] = coverage
        resMap['numFuncCovered'] = numFuncCovered
        resMap['numFunc'] = numFunc
        resMap['bitAssign'] = self.pd.bitAssign
        resMap['loss'] = 1 - coverage
        resMap['status'] = hp.STATUS_OK
        return resMap

def genSpace(nInputs, nBits):
    nBitsLut = 2 ** nInputs
    if nBits > nBitsLut:
        exit("Error in genSpace(): Invalid input: nBits")
    space = list()
    for i in range(nBitsLut):
        space.append(hp.hp.randint("b[{}]".format(i), 0, nBits+1))
    return space


def genSpaceNoGnd(nInputs, nBits):
    nBitsLut = 2 ** nInputs
    if nBits > nBitsLut:
        exit("Error in genSpace(): Invalid input: nBits")
    space = list()
    for i in range(nBitsLut):
        space.append(hp.hp.randint("b[{}]".format(i), 1, nBits+1))
    return space


def genSpaceFromInit(nInputs, nBits, bitAssignInit, spaceBeg=1):
    nBitsLut = 2 ** nInputs
    if nBits > nBitsLut:
        exit("Error in genSpace(): Invalid input: nBits")
    if spaceBeg > nBitsLut: 
        exit("Error in genSpace(): Invalid input: spaceBeg")
        
    lenInit = len(bitAssignInit)
    baInit = canonicalizeBitAssign(bitAssignInit)
    nBitsInit = max(baInit)
    if nBitsInit > nBits:
        exit("Error in genSpaceFromInit: Invalid input: bitAssignInit")
    space = list()
    space += baInit
    for i in range(lenInit, nBitsLut):
        space.append(hp.hp.randint("b[{}]".format(i), spaceBeg, nBits+1))
    return space


def genSpaceFromInit2(nInputs, nBits, bitAssignInit):
    nBitsLut = 2 ** nInputs
    if nBits > nBitsLut:
        exit("Error in genSpace(): Invalid input: nBits")
    lenInit = len(bitAssignInit)
    baInit = canonicalizeBitAssign(bitAssignInit)
    nBitsInit = max(baInit)
    if nBitsInit > nBits:
        exit("Error in genSpaceFromInit: Invalid input: bitAssignInit")
    space = list()
    space += baInit
    for i in range(lenInit, nBitsLut):
        space.append(hp.hp.randint("b[{}]".format(i), 2, nBits+1))
    return space


def genSpaceFromInitAddBit(nInputs, nBits, bitAssignInit, bitFrom, bitToList):
    nBitsLut = 2 ** nInputs
    if nBits > nBitsLut:
        exit("Error in genSpaceFromInitAddBit(): Invalid input: nBits")
    nBitsInit = max(bitAssignInit)
    if nBitsInit > nBits:
        exit("Error in genSpaceFromInitAddBit: Invalid input: bitAssignInit")
    lenInit = len(bitAssignInit)
    if lenInit < nBitsLut:
        exit("Error in genSpaceFromInitAddBit: Invalid lenInit")
        
    '''
    '''
    print("bitAssignInit: ", bitAssignInit)
    print("bitFrom: ", bitFrom)
    print("bitToList: ", bitToList)
        
    indexBitFrom = bitAssignInit.index(bitFrom)
    indexBitToList = list()
    for bitTo in bitToList:
        if bitTo in bitAssignInit:
            indexBitTo = bitAssignInit.index(bitTo)
            indexBitToList.append(indexBitTo)
        else:
            indexBitToList.append(-1)
    baInit = canonicalizeBitAssign(bitAssignInit)

    bitFrom = baInit[indexBitFrom]
    for i in range(len(bitToList)):
        indexBitTo = indexBitToList[i]
        if indexBitTo != -1:
            bitToList[i] = baInit[indexBitTo]
    print("After canonicalization: ")
    print("bitAssignInit: ", baInit)
    print("bitFrom: ", bitFrom)
    print("bitToList: ", bitToList)

    space = baInit
    cnt = 0 #number of choice
    for index in range(lenInit):
        if index < nBitsLut / 4: #keep small lut
            continue
        if space[index] == bitFrom:
            space[index] = hp.hp.choice("choice[{}]".format(cnt), [bitFrom] + bitToList)
            cnt += 1
    #print(space) 
    return space, cnt



#===========================================================================
#----- Testbench -----
if __name__ == "__main__":
    start = time.perf_counter()
    print("Now in seekDslut.py")

    nInputs = 5
    libFileName = "./dsdlib/de_test.txt"
    if False:
        libFileName = "./dsdlib/libBaseBest.txt"
        dslut_seeker = plb.DSLUT_Seeker(nInputs, libFileName)
        dslut_seeker.seekDSLUT()
        #dslut_seeker.importMatchResult("MatchResult_Sep04_1442.txt")
        dslut_seeker.exportMatchResult()
        print("libFile:", libFileName)
        exit()
        
    nBits = 6
    objective = DslutObjective(nInputs, libFileName)
    objective.pd.bitAssign = [0, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 4, 4, 2, 5, 4, 4, 3, 3, 4, 5, 6, 6, 4, 4]
    if False:
        #bitAssign = [7, 1, 10, 2, 11, 8, 12, 3, 13, 14, 15, 16, 17, 18, 19, 20,   4, 2, 3, 2, 4, 2, 3, 3, 4, 3, 3, 2, 4, 3, 3, 3, 5, 6, 6, 6, 9, 6, 6, 9, 5, 9, 6, 6, 9, 9, 6, 9, 5, 6, 9, 6, 9, 4, 9, 9, 5, 9, 9, 6, 9, 9, 9, 9]
        bitAssign = [0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 2, 2, 2, 4, 5, 2, 6, 4, 6, 7, 7, 7, 7, 8, 7, 7, 7, 9, 9, 9, 10, 9, 11, 11, 12]
        print(bitAssign)
        #res = canonicalizeBitAssign(bitAssign)
        res, cntChoice = genSpaceFromInitAddBit(nInputs, nBits, bitAssign, 2, 12)
        print(len(res))
        print("cntChoice: ", cntChoice)
        #objective(bitAssign)
        exit()
    space = genSpace(nInputs, nBits)
    trials = hp.Trials()
    #best = hp.fmin(fn=lambda x: (x-2)**2 + 1, 
    best = hp.fmin(fn=objective, 
                   space=space,
                   algo=hp.tpe.suggest, 
                   max_evals=10, 
                   trials=trials)
    print(best)
    res_sort = sorted(trials.results, key=lambda x: x['loss'])
    
    for index in range(5):
        print(res_sort[index])


    end = time.perf_counter()
    print("Running time: %s Seconds"  % (end-start))

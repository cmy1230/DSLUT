import time
import os
import re
from enum import Enum
from pysat.solvers import Solver
from random import randint
from itertools import permutations
#from numpy import dot
from multiprocessing import Pool
import platform

curOs = platform.system()
#print("Current OS: ", curOs)
if curOs == "Linux":
    flagLinux = True
elif curOs == "Windows":
    flagLinux = False
else:
    print("Unknown system")
    exit()

#----- Dot Product -----
def dot(l, r):
    res = 0
    for i in range(len(l)):
        res += l[i] * r[i]
    return res

#----- Int to TruthTable (list(bit)) -----
def int2tt(value, nVars):
    tmp = bin(value).replace('0b','')
    lenTt = 2 ** nVars
    if value >= 2 ** lenTt:
        print("Error in int2Tt(), value is too large for nVars = ", nVars)
        return None
    truthTable = [False for i in range(lenTt)]
    for i in range(len(tmp)):
        if tmp[i] == '1':
            truthTable[len(tmp)-1-i] = True;
    #print("value = ", value, "\ntruthTable = ", truthTable)
    return truthTable

#----- TruthTable (list(bit)) to Int -----    
def tt2int(tt):
    value = 0
    for i in range(len(tt)):
        if tt[i]:
            value = value + 2 ** i
    #print("tt = ", tt, "\nvalue = ", value)
    return value

#----- Compute 2 cofactors -----
def computeCofactors(tt, var):
    step = 2 ** var
    if step > len(tt)/2:
        print("Error in computeCofactors(), invalid input")
        return None
    nSteps = len(tt)//(2*step)
    cof0 = []
    cof1 = []
    for i in range(nSteps):
        for j in range(step):
            cof0.append(tt[i*2*step + j])
            cof1.append(tt[i*2*step + step + j])
    #print("cof0 = ", cof0)
    #print("cof1 = ", cof1)
    return cof0, cof1

#----- Merge 2 cofactors -----
def mergeCofactors(cof0, cof1, var):
    if len(cof0) != len(cof1):
        print("Error in mergeCofactors(), 2 cofs have different length")
        return None
    step = 2 ** var
    if step > len(cof0):
        print("Error in mergeCofactors(), invalid input 'var'")
        return None
    nSteps = len(cof0)//step
    tt = []
    for i in range(nSteps):
        for j in range(step):
            tt.append(cof0[i*step + j])
        for k in range(step):
            tt.append(cof1[i*step + k])
    #print("after merging, tt = ", tt)
    return tt

#----- Negate one specific input -----
def negateOneInput(tt, var):
    if 2 ** var > len(tt)/2:
        print("Error in negateOneInput(), invalid input var")
        return None
    c0, c1 = computeCofactors(tt, var)
    newTt = mergeCofactors(c1, c0, var)
    #print("After negating, new_tt = ", newTt)
    return newTt
    
#----- move one input to another location -----
def moveInput(tt, from_var, to_var): #other valuables keep in the same sequence
    if 2 ** from_var > len(tt)/2:
        print("Error in moveInput(), invalid input from_var")
        return None
    if 2 ** to_var > len(tt)/2:
        print("Error in moveInput(), invalid input to_var")
        return None
    if from_var == to_var:
        newTt = tt.copy()
        return newTt
    c0, c1 = computeCofactors(tt, from_var)
    newTt = mergeCofactors(c0, c1, to_var)
    #print("After moving, new_tt = ", newTt)
    return newTt

#----- swap two input -----
def swapTwoInput(tt, var0, var1):
    if var0 > var1:
        var0, var1 = var1, var0
    newTt = moveInput(tt, var0, var1)
    newTt = moveInput(newTt, var1-1, var0)
    return newTt

#----- Enumerate all input negation -----
def enumAllInputNegation(tt, nVars):
    if 2 ** nVars != len(tt):
        print("Error in enumAllInputNegation(), invalid input")
        return None
    result = set()
    for i in range(2 ** nVars):
        negateList = int2tt(i, nVars)
        tmp_tt = tt
        for j in range(len(negateList)):
            if negateList[j] == 1:
                tmp_tt = negateOneInput(tmp_tt, j)
        result.add(tt2int(tmp_tt))
    #print("After negating all inputs, result set = ", result)
    return result
        
#----- Enumerate all input permutation -----
def enumAllInputPermutation(tt, level, nVars):
    if level >= nVars:
        print("Error in enumAllInputPermutation(), invalid input")
        return None
    if level == 0:
        print("Error in enumAllInputPermutation(), invalid level")
    result = set()
    if level == 1:
        result.add(tt2int(tt))
        result.add(tt2int(moveInput(tt, 0, 1)))
        #print(level, result)
        return result
    result = result.union(enumAllInputPermutation(tt, level-1, nVars))
    for i in range(level):
        result = result.union(enumAllInputPermutation(moveInput(tt, i, level), level-1, nVars))
    #print(level, result)
    return result

#----- Analyze one function -----
def computeNPNbyEnum(tt_value, nVars):
    tt = int2tt(tt_value, nVars)
    if tt == None:
        print("Error in computeNPNbyEnum(), invalid input")
        return None
    equals = set() #for NPN equivalent functions, tt_value stored. 
    equals = enumAllInputPermutation(tt, nVars-1, nVars)
    equals_input_negation = set()
    for tt_value_i in equals:
        equals_input_negation = equals_input_negation.union(enumAllInputNegation(int2tt(tt_value_i, nVars), nVars))
    equals = equals.union(equals_input_negation)
    equals_output_negation = set()
    for tt_value_i in equals:
        equals_output_negation.add(2**len(tt)-1-tt_value_i)        
    equals = equals.union(equals_output_negation)
    '''
    print("len(equals) = ", len(equals))
    print("min(equals) = ", min(equals))
    print("equals = ", equals)
    print("----------")
    '''
    return equals

#----- Analyze all functions with the given number of inputs -----
def analyzeAllFunc(nVars):
    numFuncs = 2 ** (2 ** nVars)
    func2NPN = [-1 for i in range(numFuncs)]
    func2NPN[0] = 0
    func2NPN[numFuncs-1] = 0
    allNPNs = set()
    allNPNs.add(0)

    for tt_value in range(numFuncs):
        if func2NPN[tt_value] == -1:
            allNPNs.add(tt_value) #if the function is met at the first time, it must be a npn canonical form
            equals = computeNPNbyEnum(tt_value, nVars)
            print(len(allNPNs),' 0x%x'%tt_value, ':', int2tt(tt_value, nVars), " NumFunc for this NPN: ", len(equals))
            if min(equals) != tt_value:
                print("Fatal error!")
                return None
            for tt_value_i in equals:
                func2NPN[tt_value_i] = tt_value

    print("nVars = ", nVars)
    print("numFuncs = ", numFuncs)
    print("NumNPN = ", len(allNPNs))
    print("allNPNs = ", allNPNs)


#=================================================================
#----- Compute the ISOP of a given truth table -----
def computeIsop(tt, ttdc, nvars):
    if len(tt) != 2**nvars:
        print("Error in computeIsop(), invalid length of tt")
        exit()
    if len(tt) != len(ttdc):
        print("Error in computeIsop(), different lengths of tt and ttdc")
        exit()
    if tt2int([tt[i]&~ttdc[i] for i in range(len(tt))]) != 0:
        print("Error in computeIsop(), invalid ttdc")
        exit()
    if tt2int(tt) == 0:
        return None, [False for i in range(2**nvars)] 
    if tt2int(ttdc) == 2**len(ttdc)-1:
        return [[]], [True for i in range(2**nvars)]

    var = nvars - 1
    cof0, cof1 = computeCofactors(tt, var)
    cof0dc, cof1dc = computeCofactors(ttdc, var)

    resCovers0, resTt0 = computeIsop([ cof0[i] & ~cof1dc[i] for i in range(len(cof0))], cof0dc, var)
    resCovers1, resTt1 = computeIsop([ cof1[i] & ~cof0dc[i] for i in range(len(cof1))], cof1dc, var)
    resCovers2, resTt2 = computeIsop([ (cof0[i] & ~resTt0[i]) | (cof1[i] & ~resTt1[i]) for i in range(len(cof0))], [ cof0dc[i] & cof1dc[i] for i in range(len(cof0dc))], var)

    resCovers = []
    if resCovers0 != None:
        for cover in resCovers0:
            cover.append(-1*(var+1))
            resCovers.append(cover)

    if resCovers1 != None:
        for cover in resCovers1:
            cover.append(var+1)
            resCovers.append(cover)

    if resCovers2 != None:
        for cover in resCovers2:
            resCovers.append(cover)

    resTt = mergeCofactors([ resTt0[i] | resTt2[i] for i in range(len(resTt0))], [ resTt1[i] | resTt2[i] for i in range(len(resTt1))], var)
#    print("resCovers = ", resCovers)
#    print("resTt = ", resTt)
    return resCovers, resTt

#----- Stretch truth table -----
def stretchTt(tt, nvars_from, nvars_to):
    resTt = tt.copy()
    if len(tt) != 2**nvars_from:
        print("Error in stretchTt(), invalid inputs: nvars_from")
        exit()
    if nvars_from >= nvars_to:
        print("Error in stretchTt(), invalid inputs: nvars_to")
        exit()
    for i in range(nvars_to - nvars_from):
        resTt = mergeCofactors(resTt, resTt, nvars_from + i)
    return resTt

#----- Generate single variable truth table -----
def genSingleVarTt(var, isCompl, nvars):
    if var >= nvars:
        print("Error in genSingleVarTt(), invalid Input!")
        exit()
    if isCompl == 0:
        resTt = [False, True]
    else:
        resTt = [True, False]
    resTt = stretchTt(resTt, 1, nvars)
    resTt = moveInput(resTt, 0, var)
    return resTt

#----- Compute truth table from ISOP -----
def computeTtFromIsop(covers, nvars):
    if covers == None:
        return int2tt(0, nvars)
    resTt = int2tt(0, nvars)
    for cover in covers:
        coverTt = [True for i in range(2**nvars)]
        for var in cover:
            if abs(var) > nvars:
                print("Error in computeTtFromIsop(), invalid input: nvars")
                exit()
            varTt = genSingleVarTt(abs(var)-1, var<0, nvars)
            coverTt = [coverTt[i] & varTt[i] for i in range(len(varTt))]
        resTt = [resTt[i] | coverTt[i] for i in range(len(resTt))]
    return resTt

#----- Complement literals in the covers -----
def complementLitInCovers(covers):
    if len(covers) == 0:
        print("Error in complementLitInCovers(), invalid input")
        exit()
    for cover in covers:
        for i in range(len(cover)):
            cover[i] = -1*cover[i]
    return covers

#----- Generate CNF clauses from truth table -----
def genClausesFromTt(tt_value, nVars, varBase = 0):
    tt = int2tt(tt_value, nVars)
    tt_bar = [not i for i in tt]
    covers, resTt = computeIsop(tt_bar, tt_bar, nVars)
    if covers == None:
        return []
    resClauses = complementLitInCovers(covers)
    if varBase > 0:
        for clause in resClauses:
            for i in range(len(clause)):
                if clause[i] > 0:
                    clause[i] += (varBase-1)
                else:
                    clause[i] -= (varBase-1) 
    return resClauses

#----- composition of two functions -----
def composeTwoFuncs(tt_out, nVarsOut, tt_in, nVarsIn, var):
    '''
    F(X) = Fout(Xout, Fin(Xin))
    var is the position in Fout
    The order of vars in the Fout is ensured to be invariant
    e.g. Fout(1,2,Fin(3,4),5)
    '''
    '''
    covers, _ = computeIsop(tt_out, tt_out, nVarsOut)
    print("tt_out: ", tt_out, covers)
    covers, _ = computeIsop(tt_in, tt_in, nVarsIn)
    print("tt_in: ", tt_in, covers)
    '''

    resTt = []
    tt_tmp = moveInput(tt_out, var, 0)
    for i in range(len(tt_out)//2):
        cofactor = tt_tmp[i*2:i*2+2]
        #print("cofactor: ", cofactor)
        if cofactor == [0, 0]:
            resTt += [False for bit in tt_in]
        elif cofactor == [1, 1]:
            resTt += [True for bit in tt_in]
        elif cofactor == [0, 1]:
            resTt += [bit for bit in tt_in]
        elif cofactor == [1, 0]:
            resTt += [not bit for bit in tt_in]
        else:
            print("Error in composeTwoFuncs: invalid cofactor: ", cofactor)
            exit()
    '''
    print("After composition: resTt: ", resTt)
    covers, _ = computeIsop(resTt, resTt, nVarsOut + nVarsIn - 1)
    print("covers: ", covers)
    '''

    var_new = var + nVarsIn - 1
    for i in range(var):
        resTt = moveInput(resTt, var_new, 0)
    '''
    print("After permutation: resTt: ", resTt)
    covers, _ = computeIsop(resTt, resTt, nVarsOut + nVarsIn - 1)
    print("covers: ", covers)
    '''
    return resTt
    
#=======================================================================
#----- Enum type for Node -----
class NodeType(Enum):
    NONE = 0
    PI = 1
    PO = 2
    DSLUT = 3
    VMUX = 4
    LOGIC = 5
    LUT = 6

#----- Class of Node in PLB model for SAT (base class) -----
class Node(object):
    def __init__(self, nodeId, nodeType, nFanins):
        self.nodeId = nodeId
        self.nodeType = nodeType
        self.nFanins = nFanins
        self.faninIds = [-1 for i in range(nFanins)]
        
        self.varI = [-1 for i in range(nFanins)]
        self.varO = -1
        self.clausesGlobal = []
        self.clausesLocal = []
        self.nVarsGlobal = 0
        self.nVarsLocal = 0

    def assignFaninVarName(self, varList):
        if len(varList) != self.nFanins:
            print("Error in Node.assignVarName(), invalid input: varList")
            exit()
        for i in range(self.nFanins):
            self.varI[i] = varList[i]

    def getVarO(self):
        return self.varO

    def printNode(self):
        print("Now printing a Node object")
        print("Id = ", self.nodeId)
        print("Type = ", self.nodeType)
        print("nFanins = ", self.nFanins)
        print("faninIds = ", self.faninIds)
        print("varI = ", self.varI)
        print("varO = ", self.varO)
        print("nVarsGlobal = ", self.nVarsGlobal)
        print("clausesGlobal = ", self.clausesGlobal)

#----- Class of PI -----
class PI_Model(Node):
    def __init__(self, nodeId):
        super().__init__(nodeId, NodeType.PI, 0)

#----- Class of PO -----
class PO_Model(Node):
    def __init__(self, nodeId):
        super().__init__(nodeId, NodeType.PO, 1)

#----- Class of Logic -----
class LOGIC_Model(Node):
    def __init__(self, nodeId, nFanins, tt_value):
        super().__init__(nodeId, NodeType.LOGIC, nFanins) #nFanins is the nVars of the logic gate
        self.tt_value = tt_value
        self.tt = int2tt(tt_value, nFanins)

    def genLocalCNFClauses(self):
        '''
        The varI and varO must be assigned in advance
        '''
        for i in self.varI:
            if i == -1:
                print("Error in LOGIC.genLocalCNFClauses(): the varI is not assigned")
                exit()

        if self.varO == -1:
            print("Error in LOGIC.genLocalCNFClauses(): the varO is not assigned")
            exit()

        self.clausesLocal = []
        self.nVarsLocal = 0
        
        #Generate the truthtable of the charactistic function
        #print("tt: ", self.tt)
        tt_cnf = [not x for x in self.tt] + self.tt
        #print("tt_cnf: ", tt_cnf)
        ttv_cnf = tt2int(tt_cnf)
        #the fanout of this logic gate is the most significant variable
        #variables in the clauses are named from "1", not the actual names
        clauses = genClausesFromTt(ttv_cnf, self.nFanins + 1)
        #print("clauses: ", clauses)
        
        #map the variables in clauses to the actual varName according to varI and varO
        for clause in clauses:
            res_clause = []
            for literal in clause:
                flagC = False
                if literal < 0:
                    flagC = True
                    literal = -literal
                index = literal - 1
                if index == self.nFanins:
                    res_literal = self.varO
                elif index < self.nFanins:
                    res_literal = self.varI[index]
                else:
                    print("Error in LOGIC.genLogicCNFClauses(): out of range")
                    exit()
                if flagC:
                    res_literal = -res_literal
                res_clause.append(res_literal)
            self.clausesLocal.append(res_clause)
        
        #print("self.clausesLocal: ", self.clausesLocal)

        for i in range(len(self.varI)):
            self.varI[i] = -1
        self.varO = -1
        return self.clausesLocal
            
#----- Class of LUT model for SAT -----
class LUT_Model(Node):
    def __init__(self, nodeId, nFanins, varBase):
        super().__init__(nodeId, NodeType.LUT, nFanins) 
        self.varBaseGlobal = varBase
        self.nVarsGlobal = 2 ** nFanins
        self.tt = []
    
    def genGlobalCNFClauses(self):
        print("LUT_Model has no global clauses")
        return 0
        
    def genLocalCNFClauses(self):
        for i in self.varI:
            if i == -1:
                print("Error in LUT.genLocalCNFClauses(): the varI is not assigned")
                exit()
        if self.varO == -1:
            print("Error in LUT.genLocalCNFClauses(): the varO is not assigned")
            exit()
        
        self.clausesLocal = []
        
        #{D},{S}=>{O}
        for i in range(self.nVarsGlobal):
            Di = self.varBaseGlobal + i
            O = self.varO
            clause = [O, -Di]
            clause2 = [-O, Di]
            selList = int2tt(i, 5) #selecting bits
            for j in range(self.nFanins):
                Sj = self.varI[j]
                if selList[j] == True:
                    clause.append(-Sj)
                    clause2.append(-Sj)
                else:
                    clause.append(Sj)
                    clause2.append(Sj)
            self.clausesLocal.append(clause)
            self.clausesLocal.append(clause2)
                    
        for i in range(len(self.varI)):
            self.varI[i] = -1
        self.varO = -1

        #print("LUT.clausesLocal = ", self.clausesLocal)
        return self.clausesLocal

#----- Compute the current truth table from the given SAT result -----
    def computeTruthTable(self, sat_model):
        valueD = []
        for i in range(self.nVarsGlobal):
            varName = self.varBaseGlobal + i
            if sat_model.count(varName):
                valueD.append(True)
            elif sat_model.count(-varName):
                valueD.append(False)
            else:
                print("Error in LUT.computeTruthTable(): invalid input: sat_model")
                exit()
        
        resTt = valueD.copy()
        #print("LUT.ttv :", tt2int(resTt))
        #print("sat_model: ", sat_model)
        #print("LUT.tt: ", resTt)
        self.tt = resTt
        return resTt
        

#----- Class of VMUX model for SAT-----
class VMUX_Model(Node):
    def __init__(self, nodeId, nFanins, varBase):
        super().__init__(nodeId, NodeType.VMUX, nFanins) #nFanins is the nVars of the function to match
        self.varBaseGlobal = varBase
        self.nVarsGlobal = len(bin(nFanins-1)) - 2 #-2 means removing the "0b"
        #print("VMUX.varBaseGlobal = ", self.varBaseGlobal)
        #print("VMUX.nVarsGlobal = ", self.nVarsGlobal)
        self.genGlobalCNFClauses()

#----- Genenrate global models of VMUX (constraints for unused data input) -----
    def genGlobalCNFClauses(self):
        '''
        add the constraints for the unused data bits of the VMUX.
        Noted that, the global clauses should be re-generated for each given function to match 
        '''
        constraints = [True for i in range(self.nFanins)]
        tt_value = tt2int(constraints)
        self.clausesGlobal += genClausesFromTt(tt_value, self.nVarsGlobal, self.varBaseGlobal)
        #print("VMUX.clausesGlobal = ", self.clausesGlobal)

#----- Gnenrate local models of the VMUX (For input permutation) -----
    def genLocalCNFClauses(self): 
        for i in self.varI:
            if i == -1:
                print("Error in VMUX.genLocalCNFClauses(): the varI is not assigned")
                exit()
        if self.varO == -1:
            print("Error in VMUX.genLocalCNFClauses(): the varO is not assigned")
            exit()

        self.clausesLocal = []
        self.nVarsLocal = 0 #VMUX has no local variables for CNF clauses
        
        #MUX_Tree: {PI},{V}=>O
        VO = self.varO
        for i in range(self.nFanins):
            PIi = self.varI[i]
            clause = [VO, -PIi]
            clause2 = [-VO, PIi]
            tmp = int2tt(i, 5) #Assuming nPIs <= 32
            for j in range(self.nVarsGlobal):
                Vj = self.varBaseGlobal + j
                if tmp[j] == True:
                    clause.append(-Vj)
                    clause2.append(-Vj)
                else:
                    clause.append(Vj)
                    clause2.append(Vj)
            self.clausesLocal.append(clause)
            self.clausesLocal.append(clause2)

        '''
        print("VMUX.varBaseI = ", self.varI)
        print("VMUX.varO = ", self.varO)
        print("VMUX.clausesLocal = ", self.clausesLocal)
        '''

        for i in range(len(self.varI)):
            self.varI[i] = -1
        self.varO = -1
        return self.clausesLocal

#----- Find a PI according to sat_model -----
    def findPI(self, sat_model):
        valueV = []
        for i in range(self.nVarsGlobal):
            varName = self.varBaseGlobal + i
            if sat_model.count(varName):
                valueV.append(True)
            elif sat_model.count(-varName):
                valueV.append(False)
            else: 
                print("Error in VMUX.findPI(): invalid input: sat_model")
                exit()
        PI_index = tt2int(valueV)
        #print("PI_index for this VMUX: ", PI_index)
        return PI_index


#----- Class of DSLUT model for SAT-----
class DSLUT_Model(Node):
    '''
The given DSLUT is described by two lists: bitAssign and isCompList
When bitAssign = [i+1 for i in range(2**k)] and isCompList = [0 for i in range(2**k)] where k is the number of inputs, the DSLUT is actually a normal LUT-k.
nBits == max(bitAssign)

varBaseGlobal is the first variable ID for all the global variables of DSLUT_Model, which includes B_I, B_O, B_D and D that are global for all minterm assignment of X. 
clausesGlobal contains clauses describe the relation between B_D and D

CNF variables of DSLUT:
B_I: Bits for programmable inverters of input
B_O: Bits for programmable inverters of output
B_D: Actual programmable bits for functionality. EXCLUDING Const0
D: Data for MUX tree
The variables above are global.

I: Primary Input
S: Selecting signals for MUX tree
M_O: output of MUX tree
O: Primary Output
The variables above are local, which means they are genenrated independently for each assignment of X.

{I}=>{BI}=>{S}
            |
            V
           |\
           | |
{BD}=>{D}=>| |=>MO=>BO=>O
           | |
           |/
         MUX_Tree
    '''
    def __init__(self, nodeId, nFanins, nBits, bitAssign, isCompList, varBase):
        if len(bitAssign) != 2**nFanins:
            print("Error in DSLUT.__init__(), invalid input: bitAssign")
            exit()
        if len(isCompList) != len(bitAssign):
            print("Error in DSLUT.__init__(), invalid input: isCompList")
            exit()
        if nBits != max(bitAssign):
            print("Error in DSLUT.__init__(), invalid input: nBits")
            exit()
        if varBase < 1: #CNF model in pysat is 1-started
            print("Error in DSLUT.__init__(), invalid input: varBase")
            exit()
        super().__init__(nodeId, NodeType.DSLUT, nFanins)
        self.nBits = nBits
        self.bitAssign = bitAssign
        self.isCompList = isCompList
        self.varBaseGlobal = varBase

        self.varBaseBI = self.varBaseGlobal
        self.varBaseBO = self.varBaseBI + self.nFanins
        self.varBaseBD = self.varBaseBO + 1
        self.varBaseD = self.varBaseBD + self.nBits
        self.nVarsGlobal = self.nFanins + 1 + self.nBits + 2**self.nFanins

        self.tt = []

        '''
        print("DSLUT.varBaseBI = ", self.varBaseBI)
        print("DSLUT.varBaseBO = ", self.varBaseBO)
        print("DSLUT.varBaseBD = ", self.varBaseBD)
        print("DSLUT.varBaseD = ", self.varBaseD)
        print("DSLUT.nVarsGlobal = ", self.nVarsGlobal)
        '''

        self.genGlobalCNFClauses()

#----- Generate global models of DSLUT (B_D => D) -----
    def genGlobalCNFClauses(self):
        for i in range(len(self.bitAssign)):
            Di = self.varBaseD + i
            if self.bitAssign[i] == 0:   #D[i] is connected to constant 0/1
                if self.isCompList[i] == False:
                    self.clausesGlobal.append([-Di])
                else:
                    self.clausesGlobal.append([Di])
            else:   #D[i] is connected to programmable bit BD[j]
                BDj = self.varBaseBD + self.bitAssign[i] - 1 #bitAssign is 1-started
                if self.isCompList[i] == False:
                    self.clausesGlobal.append([Di, -BDj])
                    self.clausesGlobal.append([-Di, BDj])
                else:
                    self.clausesGlobal.append([Di, BDj])
                    self.clausesGlobal.append([-Di, -BDj])
        #print("DSLUT.clausesGlobal = ", self.clausesGlobal)

#----- Generate local models of DSLUT (MUX_Tree, I=>BI=>S, M_O=>O -----
    def genLocalCNFClauses(self, varBase, isPO = False, PO_value = 0):
        if varBase <= self.varBaseGlobal + self.nVarsGlobal - 1:
            print("Error in DSLUT.genLocalCNFClauses(), invalid input: varBase")
        for i in self.varI:
            if i == -1:
                print("Error in DSLUT.genLocalCNFClauses(): the varI is not assigned")
                exit()
        if self.varO == -1:
            print("Error in DSLUT.genLocalCNFClauses(): the varO is not assigned")
            exit()

        self.clausesLocal = []
        varBaseS = varBase
        varMO = varBaseS + self.nFanins
        self.nVarsLocal = self.nFanins + 1

        '''
        print("DSLUT.varBaseI = ", self.varI)
        print("DSLUT.varO = ", self.varO)
        print("DSLUT.varBaseS = ", varBaseS)
        print("DSLUT.varMO = ", varMO)
        print("DSLUT.nVarsLocal = ", self.nVarsLocal)
        '''

        #{I}=>{BI}=>{S}
        for i in range(self.nFanins):
            BIi = self.varBaseBI + i
            Ii = self.varI[i]
            Si = varBaseS + i
            self.clausesLocal.append([BIi, Si, -Ii])
            self.clausesLocal.append([BIi, -Si, Ii])
            self.clausesLocal.append([-BIi, Si, Ii])
            self.clausesLocal.append([-BIi, -Si, -Ii])
            
        #MO=>BO=>O
        BO = self.varBaseBO
        MO = varMO
        O = self.varO
        if isPO == False:
            self.clausesLocal.append([BO, O, -MO])
            self.clausesLocal.append([BO, -O, MO])
            self.clausesLocal.append([-BO, O, MO])
            self.clausesLocal.append([-BO, -O, -MO])
        else:
            if PO_value == 0:
                self.clausesLocal.append([BO, -MO])
                self.clausesLocal.append([-BO, MO])
            else:
                self.clausesLocal.append([BO, MO])
                self.clausesLocal.append([-BO, -MO])

        #MUX_Tree: {D},{S}=>MO
        for i in range(2**self.nFanins):
            Di = self.varBaseD + i
            clause = [MO, -Di]
            clause2 = [-MO, Di]
            selList = int2tt(i, 5) #Assuming nPIs <= 32
            for j in range(self.nFanins):
                Sj = varBaseS + j
                if selList[j] == True:
                    clause.append(-Sj)
                    clause2.append(-Sj)
                else:
                    clause.append(Sj)
                    clause2.append(Sj)
            self.clausesLocal.append(clause)
            self.clausesLocal.append(clause2)

        for i in range(len(self.varI)):
            self.varI[i] = -1
        self.varO = -1

        #print("DSLUT.clausesLocal = ", self.clausesLocal)
        return self.clausesLocal

#----- Compute current function of DSLUT with given programmable bits -----
    def computeTruthTable(self, sat_model):
        valueBI = []
        for i in range(self.nFanins):
            varName = self.varBaseBI + i
            if sat_model.count(varName):
                valueBI.append(True)
            elif sat_model.count(-varName):
                valueBI.append(False)
            else:
                print("Error in DSLUT.computeTruthTable(): invalid input: sat_model")
                exit()

        varName = self.varBaseBO
        if sat_model.count(varName):
            valueBO = True
        elif sat_model.count(-varName):
            valueBO = False
        else:
            print("Error in DSLUT.computeTruthTable(): invalid input: sat_model")
            exit()

        valueBD = []
        for i in range(self.nBits):
            varName = self.varBaseBD + i
            if sat_model.count(varName):
                valueBD.append(True)
            elif sat_model.count(-varName):
                valueBD.append(False)
            else:
                print("Error in DSLUT.computeTruthTable(): invalid input: sat_model")
                exit()

        valueD = [False for i in range(2**self.nFanins)]
        for i in range(2**self.nFanins):
            if self.bitAssign[i] == 0: #bitAssign[i] == 0 means constant 0
                if self.isCompList[i]:
                    valueD[i] = True
                else:
                    continue
            else:
                BDi = self.bitAssign[i] - 1 #bitAssign[i] is 1-started
                if valueBD[BDi]:
                    if self.isCompList[i]:
                        continue
                    else:
                        valueD[i] = True
                else:
                    if self.isCompList[i]:
                        valueD[i] = True
                    else:
                        continue

        resTt = valueD.copy()
        for i in range(self.nFanins):
            if valueBI[i]:
                resTt = negateOneInput(resTt, i)
        if valueBO:
            resTt = [not i for i in resTt]
        self.tt = resTt
        #print("DSLUT resTt: ", resTt)
        return resTt

#===========================================================================
#----- Enum type for plb -----
class PlbType(Enum):
    SINGLE_LUT = 0
    SINGLE_DSLUT = 1
    LUT_LOGIC = 2
    FRAC_LUT6 = 3
    FRAC_PLB_0 = 4 #dslut6+lut5
    FRAC_PLB_1 = 5 #dual dslut6
    FRAC_PLB_2 = 6 #dual dslut6 with mux2

#----- class PlbDescription -----
class PlbDescription(object):
    def __init__(self, type=PlbType.SINGLE_DSLUT):
        self.type = type
        self.nBits = 0
        self.bitAssign = []
        self.isCompList = []
        if type == PlbType.FRAC_LUT6:
            self.nInputsLut = 5
        if type == PlbType.LUT_LOGIC:
            self.nInputsLut = 5
        if type == PlbType.FRAC_PLB_0:
            self.nInputsLut = 5
            self.nInputsDslut = 6
        if type == PlbType.FRAC_PLB_1:
            self.nInputsDslut = 6
        if type == PlbType.FRAC_PLB_2:
            self.nInputsDslut = 6

#----- PLB_Model -----
class PLB_Model(object):
    def __init__(self, nInputs, plbDescription=None):
        self.nodes = []
        self.nNodes = 0
        self.varNew = 1
        self.nInputs = nInputs

        #nodes[nodeId].faninIds[inputId] = nodeIdFirstVmux + VMUXid
        self.inputList = [] #[(nodeId, inputId, VMUXid), ( , ) ...]
        #!!!Fatal Error, this var should not be set as a private member
        #self.clausesGlobal = [] 


        self.nNodesGlobal = 0
        self.nVarsGlobal = 0
        
        if plbDescription == None:
            self.plbType = PlbType.SINGLE_LUT
            self.genSingleDslutAsLut()
        elif plbDescription.type == PlbType.SINGLE_DSLUT:
            self.plbType = plbDescription.type
            self.genSingleDslut(plbDescription.nBits, plbDescription.bitAssign, plbDescription.isCompList)
        elif plbDescription.type == PlbType.LUT_LOGIC:
            self.plbType = plbDescription.type
            self.nInputsLut = plbDescription.nInputsLut
            self.genLUTLOGIC()
        elif plbDescription.type == PlbType.FRAC_LUT6:
            self.nInputs = 8
            self.plbType = plbDescription.type
            self.nInputsLut = plbDescription.nInputsLut
            self.genFracLUT()
        elif plbDescription.type == PlbType.FRAC_PLB_0:
            self.nInputs = 8
            self.plbType = plbDescription.type
            self.nInputsLut = plbDescription.nInputsLut
            self.nInputsDslut = plbDescription.nInputsDslut
            self.genFracDSLUT(plbDescription.nBits, plbDescription.bitAssign, plbDescription.isCompList)
        elif plbDescription.type == PlbType.FRAC_PLB_1:
            self.nInputs = 8
            self.plbType = plbDescription.type
            self.nInputsDslut = plbDescription.nInputsDslut
            self.genFracDualDSLUT(plbDescription.nBits, plbDescription.bitAssign, plbDescription.isCompList)
        elif plbDescription.type == PlbType.FRAC_PLB_2:
            self.nInputs = 8
            self.plbType = plbDescription.type
            self.nInputsDslut = plbDescription.nInputsDslut
            self.genFracDualDSLUTwithMux2(plbDescription.nBits, plbDescription.bitAssign, plbDescription.isCompList)
        #TODO: PLB network description and parsing
        else:
            print("The type of the plb is undefined!")
            exit()

#----- Generate a LUT as PLB -----
    def genSingleDslutAsLut(self):
        '''
        The sample plb is a simple LUT.
        '''
        print("A %d-input LUT is generated as the sample PLB" % self.nInputs) 

        #generate PO nodes
        node_po = PO_Model(self.nNodes)
        self.nNodes += 1
        self.nodes.append(node_po)

        #generate LUT nodes
        nBits = 2**self.nInputs
        bitAssign = [i+1 for i in range(nBits)]
        isCompList = [False for i in range(nBits)]

        node_dslut = DSLUT_Model(self.nNodes, self.nInputs, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut.nVarsGlobal
        self.nodes.append(node_dslut)
        self.nNodes += 1

        #connect nodes
        node_po.faninIds[0] = node_dslut.nodeId
        for i in range(node_dslut.nFanins):
            self.inputList.append((node_dslut.nodeId, i, i))

        self.nVarsGlobal = self.varNew - 1
        self.nNodesGlobal = self.nNodes

        #print("PLB.inputList = ", self.inputList)
        #for i in range(self.nNodes):
            #self.nodes[i].printNode()

#----- Generate a simple DSLUT as PLB -----
    def genSingleDslut(self, nBits, bitAssign, isCompList):
        print("A simple DSLUT is genenrated as the PLB")

        #generate PO nodes
        node_po = PO_Model(self.nNodes)
        self.nNodes += 1
        self.nodes.append(node_po)

        #generate DSLUT nodes
        node_dslut = DSLUT_Model(self.nNodes, self.nInputs, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut.nVarsGlobal
        self.nodes.append(node_dslut)
        self.nNodes += 1

        #connect nodes
        node_po.faninIds[0] = node_dslut.nodeId
        for i in range(node_dslut.nFanins):
            self.inputList.append((node_dslut.nodeId, i, i))

        self.nVarsGlobal = self.varNew - 1
        self.nNodesGlobal = self.nNodes

#----- Generate a PLB, which consists of a lut and an AND gate -----
    def genLUTLOGIC(self):
        print("A specific PLB is generated, which consists of a lut and a logic gate")

        #generate PO nodes
        node_po = PO_Model(self.nNodes)
        self.nNodes += 1
        self.nodes.append(node_po)

        #generate AND nodes
        #node_and = LOGIC_Model(self.nNodes, 2, 8)
        #temp: try lut2
        self.nInputs = self.nInputsLut + 1
        node_and = LUT_Model(self.nNodes, 2, self.varNew)
        self.varNew += node_and.nVarsGlobal
        self.nodes.append(node_and)
        self.nNodes += 1

        #generate LUT nodes
        node_lut = LUT_Model(self.nNodes, self.nInputsLut, self.varNew)
        self.varNew += node_lut.nVarsGlobal
        self.nodes.append(node_lut)
        self.nNodes += 1

        '''
        #generate DSLUT nodes
        node_dslut = DSLUT_Model(self.nNodes, self.nInputsDslut, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut.nVarsGlobal
        self.nodes.append(node_dslut)
        self.nNodes += 1
        '''

        #connect nodes
        if False: #logic is added from the front side of the lut
            node_po.faninIds[0] = node_lut.nodeId
            node_lut.faninIds[node_lut.nFanins - 1] = node_and.nodeId
            for i in range(node_lut.nFanins):
                if i == node_lut.nFanins - 1:
                    continue
                self.inputList.append((node_lut.nodeId, i, i))
            self.inputList.append((node_and.nodeId, 0, node_lut.nFanins - 1))
            self.inputList.append((node_and.nodeId, 1, node_lut.nFanins))
        else: #logic is added to the back side of the lut
            node_po.faninIds[0] = node_and.nodeId
            node_and.faninIds[0] = node_lut.nodeId
            for i in range(node_lut.nFanins):
                self.inputList.append((node_lut.nodeId, i, i))
            self.inputList.append((node_and.nodeId, 1, node_lut.nFanins))
    
        self.nVarsGlobal = self.varNew - 1
        self.nNodesGlobal = self.nNodes
            

#----- Generate a fracturable lut6 as PLB8, which consists of two lut5s
    def genFracLUT(self):
        print("A specific PLB is generated, which consists of two lut5s")

        #generate PO nodes
        node_po = PO_Model(self.nNodes)
        self.nNodes += 1
        self.nodes.append(node_po)

        #generate MUX nodes
        covers_mux2 = [[-1, 2], [1, 3]]
        tt_mux2 = computeTtFromIsop(covers_mux2, 3)
        ttv_mux2 = tt2int(tt_mux2)
        node_mux2 = LOGIC_Model(self.nNodes, 3, ttv_mux2)
        self.nodes.append(node_mux2)
        self.nNodes += 1

        #generate LUT nodes
        node_luts = []
        for i in range(2):
            node= LUT_Model(self.nNodes, self.nInputsLut, self.varNew)
            self.varNew += node.nVarsGlobal
            self.nodes.append(node)
            self.nNodes += 1
            node_luts.append(node)

        #connect nodes
        #PI: {A, B, C, D, E, F, G, H}
        #mux2 => po
        node_po.faninIds[0] = node_mux2.nodeId

        #output mux2: (A, lut_o, lut_o) => mux2 
        self.inputList.append((node_mux2.nodeId, 0, 0)) #H => mux2.sel
        node_mux2.faninIds[1] = node_luts[0].nodeId
        node_mux2.faninIds[2] = node_luts[1].nodeId

        #lut5[0]: {BCDEF} => lut5
        for i in range(self.nInputsLut):
            self.inputList.append((node_luts[0].nodeId, i, i+1))
            
        #lut5[0]: {GHBCD} => lut5
        self.inputList.append((node_luts[1].nodeId, 0, 6))
        self.inputList.append((node_luts[1].nodeId, 1, 7))
        self.inputList.append((node_luts[1].nodeId, 2, 1))
        self.inputList.append((node_luts[1].nodeId, 3, 2))
        self.inputList.append((node_luts[1].nodeId, 4, 3))

        self.nVarsGlobal = self.varNew - 1
        self.nNodesGlobal = self.nNodes
        #print("len(inputList): ", len(self.inputList))
        #print("inputList: ", self.inputList)
        #print("len(nodes): ", len(self.nodes))
        #for node in self.nodes:
            #node.printNode()
        
#----- Generate a fracturable dslut as PLB8, which consists of a dslut6 and a lut5 -----
    def genFracDSLUT(self, nBits, bitAssign, isCompList):
        print("A specific PLB is generated, which consists of a dslut6 and a lut5")

        #generate PO nodes
        node_po = PO_Model(self.nNodes)
        self.nNodes += 1
        self.nodes.append(node_po)

        node_pinv = LUT_Model(self.nNodes, 1, self.varNew)
        self.varNew += node_pinv.nVarsGlobal
        self.nodes.append(node_pinv)
        self.nNodes += 1

        #generate MUX nodes
        #covers_mux2 = [[-3, 1], [3, 2]]
        #tt_mux2 = computeTtFromIsop(covers_mux2, 3)
        #ttv_mux2 = tt2int(tt_mux2)
        #node_mux2 = LOGIC_Model(self.nNodes, 3, ttv_mux2)
        #self.nodes.append(node_mux2)
        covers_and = [[1, 2]]
        tt_and = computeTtFromIsop(covers_and, 2)
        ttv_and = tt2int(tt_and)
        node_and = LOGIC_Model(self.nNodes, 2, ttv_and)
        self.nodes.append(node_and)
        self.nNodes += 1

        #generate DSLUT nodes
        node_dslut = DSLUT_Model(self.nNodes, self.nInputsDslut, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut.nVarsGlobal
        self.nodes.append(node_dslut)
        self.nNodes += 1

        #generate LUT nodes
        node_lut = LUT_Model(self.nNodes, self.nInputsLut, self.varNew)
        self.varNew += node_lut.nVarsGlobal
        self.nodes.append(node_lut)
        self.nNodes += 1

        #generate three MUX4 for pin-sharing
        node_muxs = []
        self.nodeIdFirstVmux4Sharing = self.nNodes
        for i in range(3):
            node = VMUX_Model(self.nNodes, 4, self.varNew) 
            self.varNew += node.nVarsGlobal
            self.nodes.append(node)
            self.nNodes += 1
            node_muxs.append(node)

        #connect nodes
        #PI: {A, B, C, D, E, F, G, H}
        #pinv => po
        node_po.faninIds[0] = node_pinv.nodeId
        node_pinv.faninIds[0] = node_and.nodeId

        #output and: (dslut_o, lut_o) => pinv 
        node_and.faninIds[0] = node_dslut.nodeId
        node_and.faninIds[1] = node_lut.nodeId
        #self.inputList.append((node_mux2.nodeId, 2, 7)) #H => mux2.sel

        #dslut6: {ABCDEF} => dslut6
        for i in range(self.nInputsDslut):
            self.inputList.append((node_dslut.nodeId, i, i))
            
        #lut5: {G, H, mux4[0:2]} => lut5
        self.inputList.append((node_lut.nodeId, 0, 6)) #G => lut5[0]
        self.inputList.append((node_lut.nodeId, 1, 7)) #H => lut5[1]
        for i in range(3):
            node_lut.faninIds[i + 2] = node_muxs[i].nodeId

        #MUX4 for pin-sharing
        #{ABCD} => MUX4[0]
        self.inputList.append((node_muxs[0].nodeId, 0, 0))
        self.inputList.append((node_muxs[0].nodeId, 1, 1))
        self.inputList.append((node_muxs[0].nodeId, 2, 2))
        self.inputList.append((node_muxs[0].nodeId, 3, 3))

        #{ABEF} => MUX4[1]
        self.inputList.append((node_muxs[1].nodeId, 0, 0))
        self.inputList.append((node_muxs[1].nodeId, 1, 1))
        self.inputList.append((node_muxs[1].nodeId, 2, 4))
        self.inputList.append((node_muxs[1].nodeId, 3, 5))

        #{CDEF} => MUX4[2]
        self.inputList.append((node_muxs[2].nodeId, 0, 2))
        self.inputList.append((node_muxs[2].nodeId, 1, 3))
        self.inputList.append((node_muxs[2].nodeId, 2, 4))
        self.inputList.append((node_muxs[2].nodeId, 3, 5))

        self.nVarsGlobal = self.varNew - 1
        self.nNodesGlobal = self.nNodes
        #print("len(inputList): ", len(self.inputList))
        #print("inputList: ", self.inputList)
        #print("len(nodes): ", len(self.nodes))
        #for node in self.nodes:
            #node.printNode()
        
        
#----- Generate a fracturable dslut as PLB8, which consists of two identical dslut6s -----
    def genFracDualDSLUT(self, nBits, bitAssign, isCompList):
        print("A specific PLB is generated, which consists of two identical dsluts")

        #generate PO nodes
        node_po = PO_Model(self.nNodes)
        self.nNodes += 1
        self.nodes.append(node_po)

        node_pinv = LUT_Model(self.nNodes, 1, self.varNew)
        self.varNew += node_pinv.nVarsGlobal
        self.nodes.append(node_pinv)
        self.nNodes += 1

        covers_and = [[1, 2]]
        tt_and = computeTtFromIsop(covers_and, 2)
        ttv_and = tt2int(tt_and)
        node_and = LOGIC_Model(self.nNodes, 2, ttv_and)
        self.nodes.append(node_and)
        self.nNodes += 1

        #generate DSLUT nodes
        node_dslut = DSLUT_Model(self.nNodes, self.nInputsDslut, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut.nVarsGlobal
        self.nodes.append(node_dslut)
        self.nNodes += 1

        #generate the other DSLUT nodes
        node_dslut2 = DSLUT_Model(self.nNodes, self.nInputsDslut, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut2.nVarsGlobal
        self.nodes.append(node_dslut2)
        self.nNodes += 1


        #connect nodes
        #PI: {A, B, C, D, E, F, G, H}
        #and + pinv => po
        node_po.faninIds[0] = node_pinv.nodeId
        node_pinv.faninIds[0] = node_and.nodeId

        #output and: (dslut_o, dslut2_o) => and + pinv 
        node_and.faninIds[0] = node_dslut.nodeId
        node_and.faninIds[1] = node_dslut2.nodeId

        #dslut6: {ABCDEF} => dslut
        for i in range(self.nInputsDslut):
            self.inputList.append((node_dslut.nodeId, i, i))
            
        #dslut2: {G, H, F, E, D, C} => dslut2
        self.inputList.append((node_dslut2.nodeId, 0, 6)) #G => dslut2[0]
        self.inputList.append((node_dslut2.nodeId, 1, 7)) #H => dslut2[1]
        self.inputList.append((node_dslut2.nodeId, 2, 5)) #F => dslut2[2]
        self.inputList.append((node_dslut2.nodeId, 3, 4)) #E => dslut2[3]
        self.inputList.append((node_dslut2.nodeId, 4, 3)) #D => dslut2[4]
        self.inputList.append((node_dslut2.nodeId, 5, 2)) #C => dslut2[5]

        self.nVarsGlobal = self.varNew - 1
        self.nNodesGlobal = self.nNodes
        #print("len(inputList): ", len(self.inputList))
        #print("inputList: ", self.inputList)
        #print("len(nodes): ", len(self.nodes))
        #for node in self.nodes:
            #node.printNode()
        
        
#----- Generate a fracturable dslut as PLB8, which consists of two identical dslut6s, with 12 MUX2s for each input -----
    def genFracDualDSLUTwithMux2(self, nBits, bitAssign, isCompList):
        print("A specific PLB is generated, which consists of two identical dsluts")

        #generate PO nodes
        node_po = PO_Model(self.nNodes)
        self.nNodes += 1
        self.nodes.append(node_po)

        node_pinv = LUT_Model(self.nNodes, 1, self.varNew)
        self.varNew += node_pinv.nVarsGlobal
        self.nodes.append(node_pinv)
        self.nNodes += 1

        covers_and = [[1, 2]]
        tt_and = computeTtFromIsop(covers_and, 2)
        ttv_and = tt2int(tt_and)
        node_and = LOGIC_Model(self.nNodes, 2, ttv_and)
        self.nodes.append(node_and)
        self.nNodes += 1

        #generate DSLUT nodes
        node_dslut = DSLUT_Model(self.nNodes, self.nInputsDslut, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut.nVarsGlobal
        self.nodes.append(node_dslut)
        self.nNodes += 1

        #generate the other DSLUT nodes
        node_dslut2 = DSLUT_Model(self.nNodes, self.nInputsDslut, nBits, bitAssign, isCompList, self.varNew) 
        self.varNew += node_dslut2.nVarsGlobal
        self.nodes.append(node_dslut2)
        self.nNodes += 1

        #generate three MUX4 for pin-sharing
        node_muxs = []
        self.nodeIdFirstVmux4Sharing = self.nNodes
        for i in range(12):
            node = VMUX_Model(self.nNodes, 2, self.varNew) 
            self.varNew += node.nVarsGlobal
            self.nodes.append(node)
            self.nNodes += 1
            node_muxs.append(node)


        #connect nodes
        #PI: {A, B, C, D, E, F, G, H}
        #and + pinv => po
        node_po.faninIds[0] = node_pinv.nodeId
        node_pinv.faninIds[0] = node_and.nodeId

        #output and: (dslut_o, dslut2_o) => and + pinv 
        node_and.faninIds[0] = node_dslut.nodeId
        node_and.faninIds[1] = node_dslut2.nodeId

        #muxs => dslut, dslut2
        for i in range(12):
            if i < 6:
                node_dslut.faninIds[i] = node_muxs[i].nodeId
            else:
                node_dslut2.faninIds[i - 6] = node_muxs[i].nodeId

            
        #{ABCDEFGH} => muxs
        #dslut: {A,G}, {B,H}, {C,E}, {D,F}, {E,A}, {F,B}
        #dslut2: {H,C}, {G,D}, {F,A}, {E,B}, {D,H}, {C,G}
        #{A,G} => mux[0]
        self.inputList.append((node_muxs[0].nodeId, 0, 0))
        self.inputList.append((node_muxs[0].nodeId, 1, 6))

        #{B,H} => mux[1]
        self.inputList.append((node_muxs[1].nodeId, 0, 1))
        self.inputList.append((node_muxs[1].nodeId, 1, 7))

        #{C,E} => mux[2]
        self.inputList.append((node_muxs[2].nodeId, 0, 2))
        self.inputList.append((node_muxs[2].nodeId, 1, 4))

        #{D,F} => mux[3]
        self.inputList.append((node_muxs[3].nodeId, 0, 3))
        self.inputList.append((node_muxs[3].nodeId, 1, 5))

        #{E,A} => mux[4]
        self.inputList.append((node_muxs[4].nodeId, 0, 4))
        self.inputList.append((node_muxs[4].nodeId, 1, 0))

        #{F,B} => mux[5]
        self.inputList.append((node_muxs[5].nodeId, 0, 5))
        self.inputList.append((node_muxs[5].nodeId, 1, 1))

        #{H,C} => mux[6]
        self.inputList.append((node_muxs[6].nodeId, 0, 7))
        self.inputList.append((node_muxs[6].nodeId, 1, 2))

        #{G,D} => mux[7]
        self.inputList.append((node_muxs[7].nodeId, 0, 6))
        self.inputList.append((node_muxs[7].nodeId, 1, 3))

        #{F,A} => mux[8]
        self.inputList.append((node_muxs[8].nodeId, 0, 5))
        self.inputList.append((node_muxs[8].nodeId, 1, 0))

        #{E,B} => mux[9]
        self.inputList.append((node_muxs[9].nodeId, 0, 4))
        self.inputList.append((node_muxs[9].nodeId, 1, 1))

        #{D,H} => mux[10]
        self.inputList.append((node_muxs[10].nodeId, 0, 3))
        self.inputList.append((node_muxs[10].nodeId, 1, 7))

        #{C,G} => mux[11]
        self.inputList.append((node_muxs[11].nodeId, 0, 2))
        self.inputList.append((node_muxs[11].nodeId, 1, 6))


        self.nVarsGlobal = self.varNew - 1
        self.nNodesGlobal = self.nNodes
        #print("len(inputList): ", len(self.inputList))
        #print("inputList: ", self.inputList)
        #print("len(nodes): ", len(self.nodes))
        #for node in self.nodes:
            #node.printNode()
        


#----- Compute the current PLB truth table with the sat_model -----
    def computeTruthTable(self, sat_model):
        for i in range(self.nNodes):
            node = self.nodes[i]
            if node.nodeType == NodeType.DSLUT:
                node.computeTruthTable(sat_model)
            if node.nodeType == NodeType.LUT:
                node.computeTruthTable(sat_model)

        #function composition
        #nodes[0] is the PO!
        plb_tt, plb_tt_nVars = self.computeTt_rec(sat_model, 0)
        #print("plbTt before permutation: ", plb_tt)
        #print("plbTtNvars: ", plb_tt_nVars)

        #input permutation
        inputAssign = []
        for i in range(self.nInputs):
            nodeId = self.nodeIdFirstVmux + i
            inputAssign.append(self.nodes[nodeId].findPI(sat_model))

        #consider the shared pi for PLB8 consisting of two LUT5
        if self.plbType == PlbType.FRAC_LUT6:
            #{BCD} => lut5[1].CDE
            for i in range(3):
                nodeId = self.nodeIdFirstVmux + 1 + i #B,C,D
                inputAssign.append(self.nodes[nodeId].findPI(sat_model))

        #Consider the three MUX4 for pin-sharing
        if self.plbType == PlbType.FRAC_PLB_0:
            #{ABCD} => mux4[0] => lut5[2] 
            nodeMux0 = self.nodes[self.nodeIdFirstVmux4Sharing]
            index = nodeMux0.findPI(sat_model)
            nodeVmux = self.nodes[nodeMux0.faninIds[index]]
            inputAssign.append(nodeVmux.findPI(sat_model))

            #{ABEF} => mux4[1] => lut5[3] 
            nodeMux1 = self.nodes[self.nodeIdFirstVmux4Sharing + 1]
            index = nodeMux1.findPI(sat_model)
            nodeVmux = self.nodes[nodeMux1.faninIds[index]]
            inputAssign.append(nodeVmux.findPI(sat_model))

            #{CDEF} => mux4[2] => lut5[4] 
            nodeMux2 = self.nodes[self.nodeIdFirstVmux4Sharing + 2]
            index = nodeMux2.findPI(sat_model)
            nodeVmux = self.nodes[nodeMux2.faninIds[index]]
            inputAssign.append(nodeVmux.findPI(sat_model))

            #G => mux2.sel
            #nodeVmux = self.nodes[self.nodeIdFirstVmux + 7]
            #inputAssign.append(nodeVmux.findPI(sat_model))
        
        #For DualDslut: [ABCDEF, GHFEDC]
        if self.plbType == PlbType.FRAC_PLB_1:
            for i in [5, 4, 3, 2]:
                nodeId = self.nodeIdFirstVmux + i
                inputAssign.append(self.nodes[nodeId].findPI(sat_model))

        #for DualDslutMux2
        if self.plbType == PlbType.FRAC_PLB_2:
            inputAssign = []
            for i in range(12):
                nodeMux : Node= self.nodes[self.nodeIdFirstVmux4Sharing + i]
                index = nodeMux.findPI(sat_model)
                nodeVmux : Node = self.nodes[nodeMux.faninIds[index]]
                inputAssign.append(nodeVmux.findPI(sat_model))

        #print("inputAssign = ", inputAssign)
        resTt = []
        for i in range(2**self.nVarsFunc):
            PI_value = int2tt(i, 5) #Assuming nPIs <= 32
            plb_inputs = [PI_value[j] for j in inputAssign] #actual input vector to dslut
            resTt.append(plb_tt[tt2int(plb_inputs)])

        #print("plbTt: ", resTt)
        #resTtv = tt2int(resTt)
        #print("resTtv: ", hex(resTtv))
        #print("inputAssign: ", inputAssign)
        #covers, _ = computeIsop(resTt, resTt, self.nVarsFunc)
        #print("covers: ", covers)
        return resTt, inputAssign


#----- Compute the truth table of a complex plb by recursion -----
    def computeTt_rec(self, sat_model, nodeId):
        node = self.nodes[nodeId]
        if node.nodeType == NodeType.PO:
            faninId = node.faninIds[0]
            return self.computeTt_rec(sat_model, faninId)
        if node.nodeType == NodeType.VMUX:
            return [False, True], 1

        if node.nodeType == NodeType.DSLUT:
            resTt = node.tt
            res_nVars = node.nFanins
        elif node.nodeType == NodeType.LUT:
            resTt = node.tt
            res_nVars = node.nFanins
        elif node.nodeType == NodeType.LOGIC:
            resTt = node.tt
            res_nVars = node.nFanins
        else:
            print("Error in PLB.computeTt_rec(): undefined nodeType")
        
        for i in range(node.nFanins):
            index = node.nFanins - 1 - i
            faninId = node.faninIds[index]
            tt_in, tt_in_nVars = self.computeTt_rec(sat_model, faninId)
            if tt_in == [False, True]:
                continue
            resTt = composeTwoFuncs(resTt, res_nVars, tt_in, tt_in_nVars, index)
            res_nVars += tt_in_nVars - 1
        
        return resTt, res_nVars
        
        
#----- Solve the QSAT with the given function and PLB -----
    def solveQBF(self, tt_value, nVarsFunc, maxNumConflicts = -1):
        '''
        Boolean matching between the PLB and the given function.
        tt_value: the bool function to match against the PLB. 
        nVarsFunc: The number of the variables of the given function.
        '''
        flagVerbose = True
        if nVarsFunc > self.nInputs | nVarsFunc <= 0:
            print("Error in PLB_Model.solveQBF(), invalid input: nVarsFunc")
        truthTable = int2tt(tt_value, nVarsFunc)
        self.nVarsFunc = nVarsFunc

        #generate PI nodes
        self.nodeIdFirstPI = self.nNodes
        for i in range(nVarsFunc):
            node = PI_Model(self.nNodes)
            self.nNodes += 1
            self.nodes.append(node)

        #generate VMUX nodes
        self.nodeIdFirstVmux = self.nNodes
        for i in range(self.nInputs):
            node_vmux = VMUX_Model(self.nNodes, nVarsFunc, self.varNew)
            self.varNew += node_vmux.nVarsGlobal
            self.nodes.append(node_vmux)
            self.nNodes += 1

        #connect nodes
        #PI => VMUX
        for i in range(self.nInputs):
            nodeId = self.nodeIdFirstVmux + i
            for j in range(nVarsFunc):
                self.nodes[nodeId].faninIds[j] = self.nodeIdFirstPI + j

        #VMUX => PLB
        for item in self.inputList:
            nodeId, inputId, VMUXid = item
            self.nodes[nodeId].faninIds[inputId] = self.nodeIdFirstVmux + VMUXid

        #print all the nodes
        #for i in range(self.nNodes):
            #self.nodes[i].printNode()

        #Add global clauses
        clausesGlobal = []
        for i in range(self.nNodes):
            clausesGlobal += self.nodes[i].clausesGlobal
        #print("PLB clausesGlobal: ", clausesGlobal)

        #New SAT solver
        sat_solver = Solver(name = "g4")
        sat_solver.conf_budget(maxNumConflicts)
        for clause in clausesGlobal:
            sat_solver.add_clause(clause)

        minterm = 0
        for iterId in range(2**nVarsFunc):
            #print("\n---------- iterId = %d ----------" % iterId)
            #Assign new name to local variables
            for i in range(self.nNodes):
                if self.nodes[i].nodeType != NodeType.PO:
                    self.nodes[i].varO = self.varNew
                    self.varNew += 1
            for i in range(self.nNodes):
                varI = []
                for j in self.nodes[i].faninIds:
                    varI.append(self.nodes[j].varO)
                self.nodes[i].assignFaninVarName(varI)

            #print all the nodes
            #for i in range(self.nNodes):
                #self.nodes[i].printNode()

            #generate local clauses
            #minterm = iterId #for brute-force enumeration
            tmp = int2tt(minterm, 5) #input assignment
            for i in range(self.nNodes):
                if self.nodes[i].nodeType == NodeType.DSLUT:
                    self.nodes[i].genLocalCNFClauses(self.varNew)
                    self.varNew += self.nodes[i].nVarsLocal
                    for clause in self.nodes[i].clausesLocal:
                        sat_solver.add_clause(clause)
                if self.nodes[i].nodeType == NodeType.LUT:
                    self.nodes[i].genLocalCNFClauses()
                    for clause in self.nodes[i].clausesLocal:
                        sat_solver.add_clause(clause)
                if self.nodes[i].nodeType == NodeType.LOGIC:
                    self.nodes[i].genLocalCNFClauses()
                    for clause in self.nodes[i].clausesLocal:
                        sat_solver.add_clause(clause)
                if self.nodes[i].nodeType == NodeType.VMUX:
                    clauses = self.nodes[i].genLocalCNFClauses()
                    for clause in clauses:
                        sat_solver.add_clause(clause)
                if self.nodes[i].nodeType == NodeType.PI: #assign input
                    index = self.nodes[i].nodeId - self.nodeIdFirstPI
                    if tmp[index] == True:
                        clause = [self.nodes[i].varO]
                    else:
                        clause = [-self.nodes[i].varO]
                    sat_solver.add_clause(clause)
                if self.nodes[i].nodeType == NodeType.PO: #assign function output
                    if truthTable[minterm] == True:
                        clause = [self.nodes[i].varI[0]]
                    else:
                        clause = [-self.nodes[i].varI[0]]
                    sat_solver.add_clause(clause)

            res = sat_solver.solve_limited()
            values = sat_solver.get_model()

            if res == False:
                if flagVerbose:
                    print("solveQBF finished when iterId = ", iterId)
                    print("solveQBF failed!")
                sat_solver.delete()
                self.clear() #ymc: Don't forget!!!!!!!!!!
                return False, None, None

            if res == None:
                if flagVerbose:
                    print("solveQBF finished when iterId = ", iterId)
                    print("solveQBF Timeout(Max numConflicts reached)!!!!!!")
                sat_solver.delete()
                self.clear() #ymc: Don't forget!!!!!!!!!!
                return None, None, None

            resTt, pinMap = self.computeTruthTable(values)
            '''
            print("iterId = ", iterId)
            print("resTt = ", resTt)
            print("resTt_value = ", tt2int(resTt))
            '''
            res = True
            for i in range(len(truthTable)):
                if truthTable[i] != resTt[i]:
                    res = False
                    minterm = i
                    break
            if res:
                if flagVerbose:
                    print("solveQBF finished when iterId = ", iterId)
                    print("solveQBF succeeded!")
                break
        
        sat_solver.delete()
        self.clear()
        #print("plb_tt = ", resTt)
        #print("plb_tt_value = ", tt2int(resTt))
        #print("res = ", res)
        return res, tt2int(resTt), pinMap

    def clear(self):
        self.nNodes = self.nNodesGlobal
        self.varNew = self.nVarsGlobal + 1
        self.nodes[0].varI[0] = -1
        del self.nodes[self.nNodes:]


#===========================================================================
#----- Objects of the imported library -----
class Func(object):
    def __init__(self, rank, objId, nSupp, nOccurNormal, nOccurCutset, nOccurBest, dsdStr, tt_value, isUseless=1):
        self.rank = rank
        self.objId = objId
        self.nSupp = nSupp
        self.nOccurNormal = nOccurNormal
        self.nOccurCutset = nOccurCutset
        self.nOccurBest = nOccurBest
        self.dsdStr = dsdStr
        self.tt_value = tt_value
        if isUseless:
            self.isMatched = False
        else:
            self.isMatched = True
        self.id = -1
        self.flag = 0 #used for dsdlib merging
    
    def printObj(self):
        print(self.rank, end="    ")
        print(self.objId, end="    ")
        print(self.nSupp, end="    ")
        print(self.nOccurNormal, end="    ")
        print(self.nOccurCutset, end="    ")
        print(self.nOccurBest, end="    ")
        print(self.dsdStr, end="    ")
        print(hex(self.tt_value))

    def computeNPN(self):
        equals = computeNPNbyEnum(self.tt_value, self.nSupp)
        return equals

#----- Import lib.txt -----
def importLibFile(libFileName):
    print("Now in importLibFile()")
    print("Now import libfile: ", libFileName)
    funcList = []
    libFile = open(libFileName)
    line = libFile.readline()
    flagBeg = False
    while line:
        if (not flagBeg) and (line.find("ymc_begin") != -1):
            flagBeg = True
        elif line.find("ymc_end") != -1:
            flagBeg = False
        elif flagBeg:
            tmpList = line.replace(":","").split()
            if len(tmpList) == 0:
                line = libFile.readline()
                continue
            rank = int(tmpList[0])
            objId = int(tmpList[1])
            nSupp = int(tmpList[2])
            if nSupp == 0:
                line = libFile.readline()
                continue
            nOccurNormal = int(tmpList[3])
            nOccurCutset = int(tmpList[4])
            nOccurBest = int(tmpList[5])
            dsdStr = tmpList[6]
            tt_value_hex = tmpList[7].replace("tt","")
            if nSupp == 1:
                tt_value_hex = "2"
            elif nSupp < 6:
                nChar = 2**nSupp/4
                tt_value_hex = tt_value_hex[0:int(nChar)]
            #print("tt_value_hex = ", tt_value_hex)
            tt_value = int(tt_value_hex, 16)
            #TODO: May be wrong
            if False and len(tmpList) == 9:
                isUseless = int(tmpList[8])
            else:
                isUseless = 1
            funcObj = Func(rank, objId, nSupp, nOccurNormal, nOccurCutset, nOccurBest, dsdStr, tt_value, isUseless)
            funcList.append(funcObj)
        line = libFile.readline()

    libFile.close()

    #Statistics
    funcNumList = [0 for i in range(10)]
    funcOccurSumList = [0 for i in range(10)]
    funcEnumSumList = [0 for i in range(10)]
    for func in funcList:
        if func.nOccurBest == 0:
            continue
        index = func.nSupp
        funcNumList[index] += 1
        funcOccurSumList[index] += func.nOccurBest
        funcEnumSumList[index] += func.nOccurNormal
    funcNum = sum(funcNumList)
    nOccurBestSum = sum(funcOccurSumList)
    nOccurEnumSum = sum(funcEnumSumList)
    print("Total funcNum: %d\nTotal nOccurBestSum: %d\nTotal nOccurEnumSum: %d" % (funcNum, nOccurBestSum, nOccurEnumSum))
    for i in range(10):
        print("%d-input: funcNum = %d; funcOccurBestSum = %d (%f%%); funcEnumSum = %d (%f%%)" 
              % (i, funcNumList[i], funcOccurSumList[i], 100*funcOccurSumList[i]/nOccurBestSum, funcEnumSumList[i], 100*funcEnumSumList[i]/nOccurEnumSum))
        
    print("ImportLibFile() Done!")
    return funcList

#===========================================================================
#----- Generate DSLUT internal programmable bits according to the given func lib -----
class DSLUT_Seeker(object):
    def __init__(self, nInputs, libFileName):
        self.nInputs = nInputs
        self.nBits = 2**nInputs
        #self.bitAssign = [0 for i in range(2**nInputs)]
        #self.isCompList = [False for i in range(2**nInputs)]

        #Import libFile
        self.libFileName = libFileName
        self.funcList = importLibFile(libFileName)
        self.funcList = [func for func in self.funcList if (func.nSupp > 0) and (func.nSupp <= self.nInputs)]
        self.targetFuncs = [func for func in self.funcList if func.nSupp == self.nInputs]
        self.nOccurBestSum = 0

        #Merge duplicated functions
        NPNmap = dict()
        funcsNew = []
        for i in range(len(self.targetFuncs)):
            self.nOccurBestSum += self.targetFuncs[i].nOccurBest
            #self.targetFuncs[i].printObj()
            funcObj = self.targetFuncs[i]
            tt_value = funcObj.tt_value
            if tt_value in NPNmap:
                funcId = NPNmap[tt_value]
                funcsNew[funcId].nOccurNormal += funcObj.nOccurNormal
                funcsNew[funcId].nOccurCutset += funcObj.nOccurCutset
                funcsNew[funcId].nOccurBest += funcObj.nOccurBest
            else:
                NPNmap[tt_value] = len(funcsNew)
                funcsNew.append(funcObj)
        print("len(targetFuncs) = ", len(self.targetFuncs))
        print("After merging duplicated functions:\nlen(targetFuncs) = ", len(funcsNew))
        self.targetFuncs = sorted(funcsNew, key=lambda func: -1*func.nOccurBest)

        #Statistics
        nOccurSum = 0
        data2dump = []
        for i in range(min(len(self.targetFuncs),100)):
            funcObj: Func = self.targetFuncs[i]
            nOccurSum += funcObj.nOccurBest
            funcObj.printObj()
            print("%d: nOccurBest = %d\tnOccurBest percentage = %f%%\tnOccurBestSum percentage = %f%%\n"
                  % (i, funcObj.nOccurBest, 100*funcObj.nOccurBest/self.nOccurBestSum, 100*nOccurSum/self.nOccurBestSum))
            data2dump.append((funcObj.dsdStr, funcObj.nOccurBest/self.nOccurBestSum, nOccurSum/self.nOccurBestSum))
        
        if False:
            print("===================\nNow dumping data:\ndsdStr\tnOccurBestPercentage")
            for item in data2dump:
                print("{}, {}, {}".format(item[0], item[1], item[2]))

        self.targetTts = [int2tt(func.tt_value, func.nSupp) for func in self.targetFuncs]
        self.nTts = len(self.targetTts)
        self.lenTt = 2**nInputs
        self.nBitsMin = len(bin(self.nTts-1)) - 2 #-2 means removing the "0b"
        #print(self.targetTts)
        self.genTtbvMethod = str()
        self.isMatched = False
        self.pd = PlbDescription()
        self.gainThreshold = 0.05/self.lenTt
        self.nBitsMax = self.lenTt/4
        self.maxNumConflicts = 50000


#----- export results of boolean matching -----
    def exportMatchResult(self):
        if not self.isMatched:
            print("The funcLib has not been boolean-matched by this script!")
        fileName = "MatchResult_" + time.strftime("%b%d_%H%M") + ".txt"
        with open(fileName, "w") as f:
            f.write("========== Parameters ==========\n")
            f.write("libFileName: %s\n" % self.libFileName)
            f.write("plb.nInputs: %d\n" % (self.nInputs))
            f.write("plb.nBits: %d\n" % (self.pd.nBits))
            f.write("plb.bitAssign: %s\n" % (self.pd.bitAssign))
            isCompListTrueIndex = []
            for i in range(len(self.pd.isCompList)):
                if self.pd.isCompList[i]:
                    isCompListTrueIndex.append(i)
            f.write("plb.isCompListTrueIndex: %s\n" % (isCompListTrueIndex))
            f.write("ttBitVectors are generated by '%s'\n" % (self.genTtbvMethod))
            f.write("maxNumConflicts: %d\n" % (self.maxNumConflicts))
            f.write("nBitsMax: %d\n" % (self.nBitsMax))
            f.write("gainThreshold: %f\n" % (self.gainThreshold * self.lenTt))

            f.write("\n========== Statistics ==========\n")
            nOccurs = [0 for i in range(self.nInputs + 1)]
            nOccursCovered = [0 for i in range(self.nInputs + 1)]
            funcCnt = [0 for i in range(self.nInputs + 1)]
            funcCoveredCnt = [0 for i in range(self.nInputs + 1)]
            for func in self.funcList:
                if func.nSupp <= 2:
                    continue
                funcCnt[0] += 1
                funcCnt[func.nSupp] += 1
                nOccurs[0] += func.nOccurBest
                nOccurs[func.nSupp] += func.nOccurBest
    
                if func.isMatched:
                    funcCoveredCnt[0] += 1
                    funcCoveredCnt[func.nSupp] += 1
                    nOccursCovered[0] += func.nOccurBest
                    nOccursCovered[func.nSupp] += func.nOccurBest
    
            for i in range(self.nInputs + 1):
                if i == 1 or i == 2:
                    continue
                if i == 0:
                    f.write("For all funcs, numFunc coverage = %d/%d\n" % (funcCoveredCnt[0], funcCnt[0]))
                    f.write("For all funcs, nOccur coverage = %f\n" % (nOccursCovered[0]/nOccurs[0]))
                    continue
                f.write("For %d-input func, numFunc coverage = %d/%d\n" % (i, funcCoveredCnt[i], funcCnt[i]))
                f.write("For %d-input func, nOccur coverage = %f\n" % (i, nOccursCovered[i]/nOccurs[i]))
            f.write("\n========== Results of Boolean Matching ==========\n")
            #f.write("iObjId\tisMatched\n")
            f.write("%6d\t%6d\n" % (0, 1)) #const function
            f.write("%6d\t%6d\n" % (1, 1)) #single var function
            if self.isMatched:
                for func in self.funcList:
                    if func.isMatched:
                        f.write("%6d\t%6d\n" % (func.objId, func.flag))

#----- import results of boolean matching -----
#TODO: import another matched lib to merge two libs
    def importMatchResult(self, fileName, isMerged=False):
        objId2funcId = dict()

        with open(fileName) as f:
            #Import parameters
            line = f.readline()
            line = f.readline()
            while line:
                if line == "\n":
                    break
                tmpList = line.replace(":","").split()
                if tmpList[0] == "libFileName":
                    libFileName = tmpList[1]
                    if self.libFileName != libFileName:
                        print("Different dsdlibDump file!")
                        exit()
                if tmpList[0] == "plb.nInputs":
                    nInputs = int(tmpList[1])
                    if self.nInputs != nInputs:
                        print("nInputs are dismatched between the result file and plb")
                if tmpList[0] == "plb.nBits":
                    self.pd.nBits = int(tmpList[1])
                if tmpList[0] == "plb.bitAssign":
                    line = line[len(tmpList[0])+3:-2].split(', ')
                    self.pd.bitAssign = [ int(x) for x in line]
                if tmpList[0] == "plb.isCompListTrueIndex":
                    line = f.readline()
                    continue
                    self.pd.isCompList = [False for i in range(self.lenTt)]
                    line = line[len(tmpList[0])+3:-2].split(', ')
                    for i in line:
                        index = int(i)
                        self.pd.isCompList[index] = True
                if tmpList[0] == "maxNumConflicts":
                    self.maxNumConflicts = int(tmpList[1])
                if tmpList[0] == "nBitsMax":
                    self.nBitsMax = int(tmpList[1])
                if tmpList[0] == "gainThreshold":
                    self.gainThreshold = float(tmpList[1]) / self.lenTt
                line = f.readline()

            for index in range(len(self.funcList)):
                func = self.funcList[index]
                objId2funcId[func.objId] = index
                #if func.nSupp > nInputs: #For simple merging
                    #continue
                if isMerged: #For normal merging
                    continue
                func.isMatched = False

            #Import results
            flagResultBeg = False
            while line:
                if (not flagResultBeg) and (line.find("Results") != -1):
                    flagResultBeg = True
                elif flagResultBeg:
                    tmpList = line.split()
                    objId = int(tmpList[0])
                    if objId in objId2funcId:
                        index = objId2funcId[objId]
                        self.funcList[index].isMatched = True
                        self.funcList[index].flag += 1
                line = f.readline()
        if self.isMatched == False:
            self.isMatched = True

#----- boolean matching between plb and self.funcList by nProcs CPU
    def match(self, nInputsPlb, pd, funcList, nProcs, chunksize, maxNumConflicts=10000):
        self.pd = pd
        self.maxNumConflicts = maxNumConflicts
        if flagLinux:
            flagPool = True
        else:
            flagPool = True
        #boolean matching
        plb = PLB_Model(nInputsPlb, pd)
        start = time.perf_counter()
        for i in range(len(funcList)):
            funcList[i].id = i
        matcher = MatcherWrapper(plb, len(funcList), maxNumConflicts)
        if flagPool:
            with Pool(processes = nProcs) as pool:
                resMatch = pool.map(matcher, funcList, chunksize)
                pool.close()
                pool.join()
        else:
            resMatch = []
            for func in funcList:
                resMatch.append(matcher(func))
        end = time.perf_counter()
        print("seekDSLUT() runtime: %s Seconds"  % (end-start))
        self.isMatched = True

        #Statistics
        nOccurs = [0 for i in range(self.nInputs + 1)]
        nOccursCovered = [0 for i in range(self.nInputs + 1)]
        funcCnt = [0 for i in range(self.nInputs + 1)]
        funcCoveredCnt = [0 for i in range(self.nInputs + 1)]
        for i in range(len(resMatch)):
            func = funcList[i]
            isMatched, resTtValue, _ = resMatch[i]
            func.isMatched = isMatched #save the result of matching
            if func.nSupp <= 2:
                #func.printObj()
                continue

            funcCnt[0] += 1
            funcCnt[func.nSupp] += 1
            nOccurs[0] += func.nOccurBest
            nOccurs[func.nSupp] += func.nOccurBest

            if isMatched:
                nOccursCovered[0] += func.nOccurBest
                nOccursCovered[func.nSupp] += func.nOccurBest
                funcCoveredCnt[0] += 1
                funcCoveredCnt[func.nSupp] += 1

            if resTtValue == func.tt_value:
                #print("%d/%d func check succeed!" % (i, len(resMatch)))
                continue
            elif resTtValue:
                print("%d/%d func check Failed!!!" % (i, len(resMatch)))
                print("resTtValue = ", resTtValue)
                print("func.tt_value = ", func.tt_value)
                exit()
            else:
                #print("%d/%d func cannot be implemented!\n" % (i, len(resMatch)))
                continue

        for i in range(self.nInputs + 1):
            if i == 1 or i == 2:
                continue
            if i == 0:
                print("For all funcs, numFunc coverage = %d/%d" % (funcCoveredCnt[0], funcCnt[0]))
                print("For all funcs, nOccur coverage = %f" % (nOccursCovered[0]/nOccurs[0]))
                continue
            print("For %d-input func, numFunc coverage = %d/%d" % (i, funcCoveredCnt[i], funcCnt[i]))
            if nOccurs[i]:
                print("For %d-input func, nOccur coverage = %f" % (i, nOccursCovered[i]/nOccurs[i]))
        print("plb.nBits: ", pd.nBits)
        print("plb.bitAssign: ", pd.bitAssign)
        #print("plb.isCompList: ", pd.isCompList)

        if False:
            print("========== Parameters ==========")
            if flagPool:
                print("nProcs = ", nProcs)
                print("chunksize = ", chunksize)
            else:
                print("Single Process")
    
            print("maxNumConflicts = ", self.maxNumConflicts)
        #print("ttBitVectors are generated by ", self.genTtbvMethod)
        #print("nBitsMax = ", self.nBitsMax)
        #print("gainThreshold = ", self.gainThreshold * self.lenTt)

        coverage = nOccursCovered[nInputsPlb] / nOccurs[nInputsPlb]
        return coverage, funcCoveredCnt[nInputsPlb], funcCnt[nInputsPlb]


#----- generate DSLUT structure -----
    def seekDSLUT(self):
        #Parameters: 
        self.numFuncs = 4000
        chunksize = 1
        self.nBitsMax = self.lenTt/2
        if flagLinux:
            nProcs = 6
        else:
            nProcs = 8
        self.gainThreshold = 0.05/self.lenTt
        maxNumConflicts = 200000

        #Generate the ttBitVectors
        #ttBitVectors = self.genTtbvByCost()
        #ttBitVectors = self.genTtbvByDotProduct()
        numFunc = 12
        ttBitVectors = self.genTtbvFromTopFunc(numFunc)
        self.genTtbvMethod = "Top{}".format(numFunc)


        #Generate the DSLUT
        self.pd.nBits, self.pd.bitAssign, self.pd.isCompList = self.genDSLUTbyTtbv(ttBitVectors, self.nBitsMax)
        #self.pd.nBits, self.pd.bitAssign, self.pd.isCompList = self.genDSLUTbyTtbvTop20(ttBitVectors, self.nBitsMax)

        #for debugging
        if True:
            return 0

        #Parallel Boolean Matching
        self.match(self.nInputs, self.pd, self.funcList, nProcs, chunksize, maxNumConflicts)

        #Export the results of boolean matching
        self.exportMatchResult()

        return 0


#----- Generate the ttBitVectors from the most common functions -----
    def genTtbvFromTopFunc(self, numFunc):
        sumOccur = 0
        for i in range(numFunc):
            funcObj = self.targetFuncs[i]
            sumOccur += funcObj.nOccurBest / self.nOccurBestSum
        print("The proportion of the top %d functions is %f%%" % (numFunc, sumOccur*100))
        
        cost = self.nBits
        cost_prev = 0
        dot_best= -1
        ttbv_best = []
        ttBitVectors = [ [] for i in range(self.lenTt) ]
        coverage = 0
        for i in range(min(len(self.targetFuncs), numFunc)):
            print("==================== iter = ", i, "=======================")
            print("cost = %d\tcoverage = %f%%\tnFunc = %d" % (self.computeCostNew(ttBitVectors), 100*coverage, len(ttBitVectors[0])))
            #generate candidate tt_value
            #ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
            if i < 2: #!!!!!!!!!!!!!!!!!!!!!!!!!!!!!The top4 funcs are not enumed
                ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
            else:
                #ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
                ttvcs = computeNPNbyEnum(self.targetFuncs[i].tt_value, self.nInputs)
            ttbv = [vec.copy() for vec in ttBitVectors]
            for ttvc in ttvcs:
                self.addTt2BitVec(ttbv, ttvc, self.targetFuncs[i].nOccurBest)

                cost_new = self.computeCostNew(ttbv)
                if cost_new < cost:
                    ttc = int2tt(ttvc, self.nInputs)
                    ttc_dot = [ self.targetFuncs[i].nOccurBest/self.nOccurBestSum if x else 0 for x in ttc ]
                    ttbv_dot = [ sum(vec)/self.nOccurBestSum for vec in ttbv ] 
                    dot_value = dot(ttc_dot, ttbv_dot)

                    cost = cost_new
                    dot_best = dot_value
                    ttbv_best = [vec.copy() for vec in ttbv]
                elif cost_new == cost: #tie-breaker
                    ttc = int2tt(ttvc, self.nInputs)
                    ttc_dot = [ self.targetFuncs[i].nOccurBest/self.nOccurBestSum if x else 0 for x in ttc ]
                    ttbv_dot = [ sum(vec)/self.nOccurBestSum for vec in ttbv ] 
                    dot_value = dot(ttc_dot, ttbv_dot)

                    if dot_value > dot_best:
                        cost = cost_new
                        dot_best = dot_value
                        ttbv_best = [vec.copy() for vec in ttbv]

                for x in ttbv:
                    x.pop()

            deltaCost = cost - cost_prev
            deltaOccur = self.targetFuncs[i].nOccurBest / self.nOccurBestSum
            if deltaCost:
                gainPerBit = deltaOccur / deltaCost
                print("Gain: %f%%" % (100*gainPerBit))
            else:
                print("!!!!!!!!!\n!!!!!!!!!!\ndeltaCost == 0")

            ttBitVectors = [vec.copy() for vec in ttbv_best]
            cost = self.computeCostNew(ttBitVectors)
            coverage += self.targetFuncs[i].nOccurBest / self.nOccurBestSum
            print("i = %d\tcost = %d\tcoverage = %f%%\tnFunc = %d" % (i, cost, 100*coverage, len(ttBitVectors[0])))
            cost_prev = cost
            cost = self.nBits
            dot_best = -1

        #choose the representative function of the NPNs again
        coverage = 0
        for i in range(min(len(self.targetFuncs), numFunc)):
            print("==================== iter = ", i, "for second choice of rep func =======================")
            print("cost = %d\tcoverage = %f%%\tnFunc = %d" % (self.computeCostNew(ttBitVectors), 100*coverage, len(ttBitVectors[0])))
            #generate candidate tt_value
            #ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
            if i < 2:  #!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!for tuning
                ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
            else:
                #ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
                ttvcs = computeNPNbyEnum(self.targetFuncs[i].tt_value, self.nInputs)
            ttbv = [vec.copy() for vec in ttBitVectors]

            for vec in ttbv:
                del vec[0]

            for ttvc in ttvcs:
                self.addTt2BitVec(ttbv, ttvc, self.targetFuncs[i].nOccurBest)

                cost_new = self.computeCostNew(ttbv)
                if cost_new < cost:
                    ttc = int2tt(ttvc, self.nInputs)
                    ttc_dot = [ self.targetFuncs[i].nOccurBest/self.nOccurBestSum if x else 0 for x in ttc ]
                    ttbv_dot = [ sum(vec)/self.nOccurBestSum for vec in ttbv ] 
                    dot_value = dot(ttc_dot, ttbv_dot)

                    cost = cost_new
                    dot_best = dot_value
                    ttbv_best = [vec.copy() for vec in ttbv]
                elif cost_new == cost: #tie-breaker
                    ttc = int2tt(ttvc, self.nInputs)
                    ttc_dot = [ self.targetFuncs[i].nOccurBest/self.nOccurBestSum if x else 0 for x in ttc ]
                    ttbv_dot = [ sum(vec)/self.nOccurBestSum for vec in ttbv ] 
                    dot_value = dot(ttc_dot, ttbv_dot)

                    if dot_value > dot_best:
                        cost = cost_new
                        dot_best = dot_value
                        ttbv_best = [vec.copy() for vec in ttbv]

                for x in ttbv:
                    x.pop()

            deltaCost = cost - cost_prev
            deltaOccur = self.targetFuncs[i].nOccurBest / self.nOccurBestSum
            if deltaCost:
                gainPerBit = deltaOccur / deltaCost
                print("Gain: %f%%" % (100*gainPerBit))
            else:
                print("!!!!!!!!!\n!!!!!!!!!!\ndeltaCost == 0")

            ttBitVectors = [vec.copy() for vec in ttbv_best]
            cost = self.computeCostNew(ttBitVectors)
            coverage += self.targetFuncs[i].nOccurBest / self.nOccurBestSum
            print("i = %d\tcost = %d\tcoverage = %f%%\tnFunc = %d" % (i, cost, 100*coverage, len(ttBitVectors[0])))
            cost_prev = cost
            cost = self.nBits
            dot_best = -1
            
            
            
        for vec in ttBitVectors:
            print(vec)
        cost = self.computeCostNew(ttBitVectors)
        print("cost = ", cost)
        #ttBitP = [ sum(vec) / self.nOccurBestSum for vec in ttBitVectors ]
        #print(ttBitP)
        return ttBitVectors
        

#----- Generate the ttBitVectors by dot-product -----
    def genTtbvByDotProduct(self, numFunc = 0):
        cost = self.nBits
        cost_prev = 0
        dot_best= -1
        ttbv_best = []
        ttBitVectors = [ [] for i in range(self.lenTt) ]
        coverage = 0
        if numFunc == 0:
            numFunc = self.numFuncs
        for i in range(min(len(self.targetFuncs), numFunc)):
            print("==================== iter = ", i, "=======================")
            #print("cost = %d\tcoverage = %f%%\tnFunc = %d" % (self.computeCost(ttBitVectors), 100*coverage, len(ttBitVectors[0])))
            #generate candidate tt_value
            ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
            #ttvcs = computeNPNbyEnum(self.targetFuncs[i].tt_value, self.nInputs)
            if i == 0:
                self.addTt2BitVec(ttBitVectors, min(ttvcs), self.targetFuncs[i].nOccurBest)
                coverage += self.targetFuncs[i].nOccurBest / self.nOccurBestSum
                continue
            ttbv = [vec.copy() for vec in ttBitVectors]
            for ttvc in ttvcs:
                self.addTt2BitVec(ttbv, ttvc, self.targetFuncs[i].nOccurBest)

                ttc = int2tt(ttvc, self.nInputs)
                ttc_dot = [ self.targetFuncs[i].nOccurBest/self.nOccurBestSum if x else 0 for x in ttc ]
                ttbv_dot = [ sum(vec)/self.nOccurBestSum for vec in ttbv ] 
                
                if sum(ttbv_dot) == 0:
                    continue
                dot_value = dot(ttc_dot, ttbv_dot)

                if dot_value > dot_best:
                    dot_best = dot_value
                    ttbv_best = [vec.copy() for vec in ttbv]

                for x in ttbv:
                    x.pop()


            ttBitVectors = [vec.copy() for vec in ttbv_best]
            cost = self.computeCost(ttBitVectors)
            coverage += self.targetFuncs[i].nOccurBest / self.nOccurBestSum
            print("i = %d\tcost = %d\tcoverage = %f%%\tnFunc = %d" % (i, cost, 100*coverage, len(ttBitVectors[0])))
            dot_best = -1

        #for vec in ttBitVectors:
            #print(vec)
        cost = self.computeCost(ttBitVectors)
        print("cost = ", cost)
        ttBitP = [ sum(vec) / self.nOccurBestSum for vec in ttBitVectors ]
        print(ttBitP)
        return ttBitVectors

#----- Generate the ttBitVectors by cost computation -----
    def genTtbvByCost(self):
        cost = self.nBits
        cost_prev = 0
        dot_best= -1
        ttbv_best = []
        ttBitVectors = [ [] for i in range(self.lenTt) ]
        coverage = 0
        for i in range(min(len(self.targetFuncs), self.numFuncs)):
            print("==================== iter = ", i, "=======================")
            print("cost = %d\tcoverage = %f%%\tnFunc = %d" % (self.computeCost(ttBitVectors), 100*coverage, len(ttBitVectors[0])))
            #generate candidate tt_value
            ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
            #ttvcs = computeNPNbyEnum(self.targetFuncs[i].tt_value, self.nInputs)
            ttbv = [vec.copy() for vec in ttBitVectors]
            for ttvc in ttvcs:
                self.addTt2BitVec(ttbv, ttvc, self.targetFuncs[i].nOccurBest)

                cost_new = self.computeCost(ttbv)
                if cost_new < cost:
                    ttc = int2tt(ttvc, self.nInputs)
                    ttc_dot = [ self.targetFuncs[i].nOccurBest/self.nOccurBestSum if x else 0 for x in ttc ]
                    ttbv_dot = [ sum(vec)/self.nOccurBestSum for vec in ttbv ] 
                    dot_value = dot(ttc_dot, ttbv_dot)

                    cost = cost_new
                    dot_best = dot_value
                    ttbv_best = [vec.copy() for vec in ttbv]
                elif cost_new == cost: #tie-breaker
                    ttc = int2tt(ttvc, self.nInputs)
                    ttc_dot = [ self.targetFuncs[i].nOccurBest/self.nOccurBestSum if x else 0 for x in ttc ]
                    ttbv_dot = [ sum(vec)/self.nOccurBestSum for vec in ttbv ] 
                    dot_value = dot(ttc_dot, ttbv_dot)

                    if dot_value > dot_best:
                        cost = cost_new
                        dot_best = dot_value
                        ttbv_best = [vec.copy() for vec in ttbv]

                for x in ttbv:
                    x.pop()

            deltaCost = cost - cost_prev
            deltaOccur = self.targetFuncs[i].nOccurBest / self.nOccurBestSum
            if deltaCost:
                gainPerBit = deltaOccur / deltaCost
                print("Gain: %f%%" % (100*gainPerBit))
            else:
                print("!!!!!!!!!\n!!!!!!!!!!\ndeltaCost == 0")

            if deltaOccur < self.gainThreshold:
                print("nOccur is too small, skip all the following funcs")
                break
            #Threshold for adding more bits
            if (deltaCost != 0) and (deltaOccur / deltaCost < self.gainThreshold):
                print("Gain is too small, skip this func")
                cost = self.nBits
                dot_best = -1
                continue

            ttBitVectors = [vec.copy() for vec in ttbv_best]
            cost = self.computeCost(ttBitVectors)
            coverage += self.targetFuncs[i].nOccurBest / self.nOccurBestSum
            print("i = %d\tcost = %d\tcoverage = %f%%\tnFunc = %d" % (i, cost, 100*coverage, len(ttBitVectors[0])))
            cost_prev = cost
            cost = self.nBits
            dot_best = -1
        #for vec in ttBitVectors:
            #print(vec)
        cost = self.computeCost(ttBitVectors)
        print("cost = ", cost)
        #ttBitP = [ sum(vec) / self.nOccurBestSum for vec in ttBitVectors ]
        #print(ttBitP)
        return ttBitVectors

#----- generate DSLUT by fully enumeration -----
#Too expensive
    def genTtbvByEnum(self, numFunc):
        print("Now in genTtbvByEnum()")
        pools = []
        candidates = [[]]
        cost_best = self.nBits
        ttbv_best = []
        for i in range(min(self.nTts, numFunc)):
            ttvcs = self.genCandidateTt(self.targetFuncs[i].tt_value)
            #ttvcs = self.targetFuncs[i].computeNPN()
            pools.append(ttvcs)
        for pool in pools:
            candidates = [x+[y] for x in candidates for y in pool]
        #print(candidates)
        print("number of possible ttBitVectors: ", len(candidates))
        return 0
        for candidate in candidates:
            ttbv = [ [] for i in range(self.lenTt) ]
            for i in range(len(candidate)):
                tt_value = candidate[i]
                self.addTt2BitVec(ttbv, tt_value, self.targetFuncs[i].nOccurBest)
            cost = self.computeCost(ttbv)
            if cost < cost_best:
                cost_best = cost
                ttbv_best = [ vec.copy() for vec in ttbv ]
        print("cost = ", cost_best)
        for vec in ttbv_best:
            print(vec)
        print("cost_check = ", self.computeCost(ttbv_best))
        return ttbv_best

#----- Generate DSLUT from ttbv of Top20 -----
#----- assign bits by similarity, but doesn't work as expected
    def genDSLUTbyTtbvTop20(self, ttbv, nBitsMax):
        print("Now in genDSLUTbyTtbv")
        if len(ttbv) != self.lenTt:
            print("Error in genDSLUTbyTtbv: invalid input")
        vecSum = [ sum(vec) for vec in ttbv ]
        nBits = self.lenTt
        if nBitsMax > nBits:
            nBitsMax = nBits
        bitAssign = [-1 for i in range(nBits)]
        isCompList = [False for i in range(nBits)]
        nBitsCur = 0

        #detect all "1" bit
        flags = [0 for vec in ttbv]
        for i in range(len(ttbv)):
            vec = ttbv[i]
            flag = True
            for x in vec:
                if x == 0:
                    flag = False
            if flag:
                flags[i] = 1

        #Ideal situations
        count0 = 0
        count1 = 0
        countsame = 0
        bitRemove = set()
        flagSame = False
        for i in range(len(ttbv)):
            vec = ttbv[i] #const0
            if vecSum[i] == 0:
                bitAssign[i] = 0
                count0 += 1
                continue
            if flags[i]: #const1
                bitAssign[i] = 0
                isCompList[i] = True
                count1 += 1
                continue
            if i in bitRemove:
                continue
            for j in range(i+1, self.lenTt):
                if ttbv[i] == ttbv[j]:
                    flagSame = True
                    countsame += 1
                    bitAssign[j] = nBitsCur + 1
                    bitRemove.add(j)
            if flagSame:
                bitAssign[i] = nBitsCur + 1
                nBitsCur += 1
                flagSame = False
        print("For ideal situations:\nconst0: %d\tconst1: %d\tSamebit: %d\tnBitsCur = %d" % (count0, count1, countsame, nBitsCur))

        #statistic-based
        nBitsUnassigned = nBits - (count1 + count0 + countsame + nBitsCur)
        print("Excluding the ideal situations, the unassigned nBits = ", nBitsUnassigned)
        print("After ideal assignment, bitAssign = ", bitAssign)
        bits = []  #unassigned bits
        for i in range(len(ttbv)):
            if bitAssign[i] != -1:
                continue
            p = vecSum[i] / self.nOccurBestSum
            bits.append( (i, p) )

        print("nBitsUnassigned = ", nBitsUnassigned, "len(bits) = ", len(bits))
        print("Unassigned bits: ", bits)
        #bitsSorted = sorted(bits, key=lambda bit: -1 * (bit[1]-0.5)**2)
        bitsSorted = sorted(bits, key=lambda bit: bit[1])
        print("Sorted unassigned bits", bitsSorted)
        flagFirstConst1 = True
        #Only one bit connected to const1, others are connected to the bit "SecConst1"
        bitForSecConst1 = -1  
        for (index, p) in bitsSorted:
            if bitAssign[index] != -1:
                continue
            if nBitsUnassigned <= nBitsMax - nBitsCur: 
                bitAssign[index] = nBitsCur + 1
                nBitsCur += 1
                nBitsUnassigned -= 1
                continue
            else: #const0
                vec_cur = ttbv[index]
                vec_cur_dot = [ x / self.nOccurBestSum for x in vec_cur ]
                dot_best = -1
                index_similar = -1
                for ivec in range(len(ttbv)):
                    if ivec == index:
                        continue
                    if ivec == 0:
                        continue
                    vec_iter = ttbv[ivec]
                    vec_iter_dot = [ x / self.nOccurBestSum for x in vec_iter ]
                    dot_res = dot(vec_cur_dot, vec_iter_dot)
                    if dot_res > dot_best:
                        dot_best = dot_res
                        index_similar = ivec
                print("index_similar of %d is %d, whose assigned bit is %d" % (index, index_similar, bitAssign[index_similar]))
                
                if bitAssign[index_similar] == -1:
                    bitAssign[index_similar] = 0
                    bitAssign[index] = 0
                    print("bit %d and %d are both set to zero" % (index, index_similar))
                    nBitsUnassigned -= 2
                else:
                    bitAssign[index] = bitAssign[index_similar]
                    print("bit %d is set to %d" % (index, index_similar))
                    nBitsUnassigned -= 1
            
        print("After assignment, nBitsUnassigned = ", nBitsUnassigned)
        print("bitAssign: \n", bitAssign)
        print("isCompList: \n", isCompList)
        print("nBitsCur = ", nBitsCur)
        return (nBitsCur, bitAssign, isCompList)

#----- Generate DSLUT from ttbv -----
    def genDSLUTbyTtbv(self, ttbv, nBitsMax):
        print("Now in genDSLUTbyTtbv")
        if len(ttbv) != self.lenTt:
            print("Error in genDSLUTbyTtbv: invalid input")
        vecSum = [ sum(vec) for vec in ttbv ]
        nBits = self.lenTt
        if nBitsMax > nBits:
            nBitsMax = nBits
        bitAssign = [-1 for i in range(nBits)]
        isCompList = [False for i in range(nBits)]
        nBitsCur = 0

        #detect all "1" bit
        flags = [0 for vec in ttbv]
        for i in range(len(ttbv)):
            vec = ttbv[i]
            flag = True
            for x in vec:
                if x == 0:
                    flag = False
            if flag:
                flags[i] = 1

        #Ideal situations
        count0 = 0
        count1 = 0
        countsame = 0
        bitRemove = set()
        flagSame = False
        for i in range(len(ttbv)):
            vec = ttbv[i]
            if vecSum[i] == 0:
                bitAssign[i] = 0
                count0 += 1
                continue
            if flags[i]:
                bitAssign[i] = 0
                isCompList[i] = True
                count1 += 1
                continue
            if i in bitRemove:
                continue
            for j in range(i+1, self.lenTt):
                if ttbv[i] == ttbv[j]:
                    flagSame = True
                    countsame += 1
                    bitAssign[j] = nBitsCur + 1
                    bitRemove.add(j)
            if flagSame:
                bitAssign[i] = nBitsCur + 1
                nBitsCur += 1
                flagSame = False
        print("For ideal situations:\nconst0: %d\tconst1: %d\tSamebit: %d\tnBitsCur = %d" % (count0, count1, countsame, nBitsCur))

        #statistic-based
        nBitsUnassigned = nBits - (count1 + count0 + countsame + nBitsCur)
        print("Excluding the ideal situations, the unassigned nBits = ", nBitsUnassigned)
        print("After ideal assignment, bitAssign = ", bitAssign)
        bits = []
        for i in range(len(ttbv)):
            if bitAssign[i] != -1:
                continue
            p = vecSum[i] / self.nOccurBestSum
            bits.append( (i, p) )

        print("nBitsUnassigned = ", nBitsUnassigned, "len(bits) = ", len(bits))
        print("Unassigned bits: ", bits)
        #bitsSorted = sorted(bits, key=lambda bit: -1 * (bit[1]-0.5)**2)
        bitsSorted = sorted(bits, key=lambda bit: bit[1])
        print("Sorted unassigned bits", bitsSorted)
        flagFirstConst1 = True
        #Only one bit connected to const1, others are connected to the bit "SecConst1"
        bitForSecConst1 = -1  
        for (index, p) in bitsSorted:
            if index in bitRemove:
                continue
            if nBitsUnassigned <= nBitsMax - nBitsCur: 
                bitAssign[index] = nBitsCur + 1
                nBitsCur += 1
                nBitsUnassigned -= 1
                continue
            else: #const0
                bitAssign[index] = 0
                nBitsUnassigned -= 1
            '''
            if p > 0.5: #const1
                if flagFirstConst1: #ensure that there is only one const1
                    bitAssign[index] = 0
                    isCompList[index] = True
                    nBitsUnassigned -= 1
                    flagFirstConst1 = False
                elif bitForSecConst1 == -1: #generate one more bit
                    bitForSecConst1 = nBitsCur + 1
                    bitAssign[index] = bitForSecConst1
                    nBitsCur += 1
                    nBitsUnassigned -= 1
                else:
                    bitAssign[index] = bitForSecConst1
                    nBitsUnassigned -= 1
            else: #const0
                bitAssign[index] = 0
                nBitsUnassigned -= 1
            '''
            
        print("After assignment, nBitsUnassigned = ", nBitsUnassigned)
        print("bitAssign: \n", bitAssign)
        print("isCompList: \n", isCompList)
        print("nBitsCur = ", nBitsCur)
        return (nBitsCur, bitAssign, isCompList)

#----- Add tt to ttBitVectors -----
    def addTt2BitVec(self, ttbv, tt_value, nOccurBest):
        tt = int2tt(tt_value, self.nInputs)
        if len(tt) != len(ttbv):
            print("Error in addTt2BitVec(): invalid input")
            exit()
        for i in range(len(tt)):
            if tt[i]:
                ttbv[i].append(nOccurBest)
            else:
                ttbv[i].append(0)

#----- generate candidate truth tables for seeking DSLUT -----
    def genCandidateTt(self, tt_value):
        tt = int2tt(tt_value, self.nInputs)
        #covers, _ = computeIsop(tt, tt, self.nInputs)
        #print("covers: ", covers)

        #output phase
        nOnes = sum(tt)
        flagOutputPhase = False
        #print("nOnes = ", nOnes)
        if nOnes*2 > len(tt):
            tt = [not x for x in tt]
        if nOnes*2 == len(tt):
            flagOutputPhase = True
            #print("balanced output phase")

        #input phase
        nOnesCof = []
        phase2enum = []
        for i in range(self.nInputs):
            cof0, cof1 = computeCofactors(tt, i)
            if sum(cof0)*2 < nOnes:
                tt = mergeCofactors(cof1, cof0, i)
            nOnesCof.append(sum(cof0))
            if nOnesCof[i] == nOnes/2:
                phase2enum.append(i)

        #input permutation
        #print("nOnesCof = ", nOnesCof)
        #print("phase2enum = ", phase2enum)
        groups = []
        i = 0
        while i < self.nInputs-1:
            group = set()
            for j in range(i+1, self.nInputs):
                if nOnesCof[i] == nOnesCof[j]:
                    group.add(j)
                else:
                    break
            if len(group) > 0:
                group.add(i)
                groups.append(group)
            i = j
        #print("groups before test of symmetry:", groups)
        
        #test symmetry
        for group in groups:
            groupList = list(group)
            for i in range(len(groupList)):
                if groupList[i] not in group:
                    continue
                var0 = groupList[i]
                for j in range(i+1, len(groupList)):
                    if groupList[i] not in group:
                        continue
                    var1 = groupList[j]
                    if tt == swapTwoInput(tt, var0, var1):
                        group.remove(var1)
        groups = [tuple(group) for group in groups if len(group) > 1]
        #print("groups after test of symmetry: ", groups)
        groupsPerm = [list(permutations(x)) for x in groups]
        pools = [list(pool) for pool in groupsPerm]
        permList = [[]]
        for pool in pools:
            permList = [x+[y] for x in permList for y in pool]
        #print("Final iter list:", permList)
        #print("len(permList) = ", len(permList))

        resTts = list()
        if (len(permList) == 1) and permList[0] == []:
            resTts.append(tt)
        elif len(permList) * (2**len(phase2enum)) > 10000:
            print("Too expensive for genCandidate(), skip permutation")
            resTts.append(tt)
        else:
            for perm in permList:
                newTt = tt.copy()
                for i in range(len(perm)):
                    groupNew = list(perm[i])
                    groupOld = list(groups[i])
                    for j in range(len(groupNew)):
                        if groupNew[j] > groupOld[j]:
                            newTt = moveInput(newTt, groupNew[j], groupOld[j]) 
                            for k in range(j+1, len(groupNew)):
                                if groupNew[k] in range(groupOld[j], groupNew[j]):
                                    groupNew[k] += 1
                        elif groupNew[j] < groupOld[j]:
                            newTt = moveInput(newTt, groupNew[j], groupOld[j])
                            for k in range(j+1, len(groupNew)):
                                if groupNew[k] in range(groupNew[j], groupOld[j]):
                                    groupNew[k] -= 1
                resTts.append(newTt)
    
    
            '''
            for tti in resTts:
                covers, _ = computeIsop(tti, tti, self.nInputs)
                print("covers: ", covers)
            '''
    
        result = set()
        for tti in resTts:
            for i in range(2**len(phase2enum)):
                negateList = int2tt(i, len(phase2enum))
                tmp_tt = tti
                for j in range(len(negateList)):
                    if negateList[j] == 1:
                        tmp_tt = negateOneInput(tmp_tt, phase2enum[j])
                result.add(tt2int(tmp_tt))

        if flagOutputPhase:
            result_o = set()
            for ttv in result:
                result_o.add(2**len(tt)-1-ttv)
            result = result.union(result_o)


        '''
        for ttv in result:
            tti = int2tt(ttv, self.nInputs)
            covers, _ = computeIsop(tti, tti, self.nInputs)
            print("covers: ", covers)
        '''

        print("The number of the candidate tts: ", len(result))
        return result

#----- compute the cost of a ttbv of top20 functions-----
    def computeCostNew(self, ttBitVectors): 
        cost = self.nBits
        #for tt in self.targetTts:
            #print(tt)
        #for vec in ttBitVectors:
            #print(vec)
        #Add occur info
        ttBitP = [sum(vec)/self.nOccurBestSum for vec in ttBitVectors]

        #detect all "1" bit
        '''
        flags = [0 for vec in ttBitVectors]
        for i in range(len(ttBitVectors)):
            vec = ttBitVectors[i]
            flag = True
            for x in vec:
                if x == 0:
                    flag = False
            if flag:
                flags[i] = 1
        '''

                
        #ttBitP = [sum(vec) for vec in ttBitVectors]
        #print(ttBitP)

        bitRemove = set()
        bitBeg = 0
        for i in range(self.lenTt):
            if True and i >= bitBeg and i < bitBeg + self.nBits/4:
                continue
            if (ttBitP[i] == 0):
                #print("nBits reduced due to constant 0 input")
                cost -= 1
                continue
            #if flags[i]:
            if False:
                #print("nBits reduced due to constant 1 input")
                cost -= 1
                continue
            if i in bitRemove:
                continue
            for j in range(i+1, self.lenTt):
                if True and j >= bitBeg and j < bitBeg + self.nBits/4:
                    continue
                if ttBitP[i] == ttBitP[j]:
                    if ttBitVectors[i] == ttBitVectors[j]:
                        #print("nBits reduced due to the same ttBitVector")
                        cost -= 1
                        bitRemove.add(j)
                        continue

        #print("Cost = ", cost)
        return cost


#----- compute the number of programmable bits for a given tt list -----
#TODO: add "OR" gate for MUX data bit control
    def computeCost(self, ttBitVectors): 
        cost = self.nBits
        #for tt in self.targetTts:
            #print(tt)
        #for vec in ttBitVectors:
            #print(vec)
        #Add occur info

        ttBitP = [sum(vec)/self.nOccurBestSum for vec in ttBitVectors]

        #detect all "1" bit
        '''
        flags = [0 for vec in ttBitVectors]
        for i in range(len(ttBitVectors)):
            vec = ttBitVectors[i]
            flag = True
            for x in vec:
                if x == 0:
                    flag = False
            if flag:
                flags[i] = 1
        '''

                
        #ttBitP = [sum(vec) for vec in ttBitVectors]
        #print(ttBitP)

        bitRemove = set()
        for i in range(self.lenTt):
            if (ttBitP[i] == 0):
                #print("nBits reduced due to constant 0 input")
                cost -= 1
                continue
            #if flags[i]:
            if False:
                #print("nBits reduced due to constant 1 input")
                cost -= 1
                continue
            if i in bitRemove:
                continue
            for j in range(i+1, self.lenTt):
                if ttBitP[i] == ttBitP[j]:
                    if ttBitVectors[i] == ttBitVectors[j]:
                        #print("nBits reduced due to the same ttBitVector")
                        cost -= 1
                        bitRemove.add(j)
                        continue

        #print("Cost = ", cost)
        return cost

#----- global process wrapper -----
class MatcherWrapper(object):
    def __init__(self, plb, nFuncs, maxNumConf):
        self.plb = plb
        self.nFuncs = nFuncs
        self.maxNumConf = maxNumConf
    def __call__(self, func):
        if True:
            print("========== %d/%d ==========\n%d-input func: %s" % (func.id, self.nFuncs-1, func.nSupp, hex(func.tt_value)))
        start = time.perf_counter()
        res, resTt, pinMap = self.plb.solveQBF(func.tt_value, func.nSupp, self.maxNumConf)
        if False:
            if res and not func.isMatched:
                print("res == True and func.isMatched == False")
                exit()
            if func.isMatched and not res:
                print("res == False and func.isMatched == True")
                exit()
        #print("%d/%d done" % (func.id+1, self.nFuncs))
        end = time.perf_counter()
        if True:
            print("%d/%d %d-input func runtime: %s Seconds"  % (func.id, self.nFuncs-1, func.nSupp, end-start))
        if False:
            print("%d-input func runtime: %s Seconds"  % (func.nSupp, end-start))
        return res, resTt, pinMap

#----- parse the abcIf result file -----
def parseAbcIfResultFile(fileName):
    with open(fileName, "r") as f:
        line = f.readline()
        item = dict()
        resVector = list()
        while line:
            searchObj = re.search(r'Now read_blif.*/(\S+)\.blif\n', line)
            if searchObj:
                item['name'] = searchObj.group(1)
                line = f.readline()
                continue
            
            searchObj = re.search(r'K\s*=\s*(\d+)',line)
            if searchObj:
                item['K'] = int(searchObj.group(1))
                line = f.readline()
                continue

            searchObj = re.search(r'nd\s*=\s*(\d+).*lev\s*=\s*(\d+)',line)
            if searchObj:
                item['nLuts'] = int(searchObj.group(1))
                item['lev'] = int(searchObj.group(2))
                resVector.append(item.copy()) 
                line = f.readline()
                continue

            line = f.readline()
    #for item in resVector:
        #print(item)
    return resVector

#----- call abcIf for mapping to LUT -----
def abcMapToLut(blifFile, K):
    resPath = os.getcwd() + '/result'
    if os.path.isdir(resPath):
        print(resPath, "exists.")
    else:
        os.mkdir(resPath)
        print(resPath, "is newly created.")
    path, fileName = os.path.split(blifFile)
    netlistName, fileExt = os.path.splitext(fileName)
    if fileExt == '':
        fileName = fileName + '.blif'
    elif fileExt != '.blif':
        print("Error in abcMapToLut(): invalid file extension")

    tmpFileName = netlistName + '_LUT' + str(K) + '.txt'
    cmd = 'abc -c "read_blif %s; if -K %d; print_stats" > %s' \
        % (os.path.join(path, fileName), K, os.path.join(resPath, tmpFileName)) 
    print(cmd)
    os.system(cmd)

    resVector = parseAbcIfResultFile(os.path.join(resPath, tmpFileName))
    res = resVector[0]
    return res['nLuts'], res['lev']

#----- call abcIf for mapping to DSLUT -----
def abcMapToDslut(blifFile, libFile, matchResFile, K):
    print("Now in abcMapToDslut()")
    print("blifFile: ", blifFile)
    print("libFile: ", libFile)
    print("matchResFile: ", matchResFile)

    resPath = os.getcwd() + '/result'
    if os.path.isdir(resPath):
        print(resPath, "exists.")
    else:
        os.mkdir(resPath)
        print(resPath, "is newly created.")

    srcPath, blifFileName = os.path.split(blifFile)
    netlistName, blifFileExt = os.path.splitext(blifFileName)
    if blifFileExt == '':
        blifFileName = blifFileName + '.blif'
    elif blifFileExt != '.blif':
        print("Error in abcMapToLut(): invalid blifFile extension")

    tmpFileName = netlistName + '_DSLUT' + str(K) + '.txt'
    cmd = 'abc -c "dsd_load %s; import_match_result %s; read_blif %s; if -k -K %d; print_stats" > %s' \
        % (libFile, matchResFile, os.path.join(srcPath, blifFileName), K, os.path.join(resPath, tmpFileName)) 
    print(cmd)
    os.system(cmd)

    resVector = parseAbcIfResultFile(os.path.join(resPath, tmpFileName))
    res = resVector[0]
    return res['nLuts'], res['lev']

#----- DSLUT area modeling -----
#TODO
class DSLUT_Area_Model(object):
    def __init__(self, nInputs, plbDescription=None):
        pass

#----- Mux Tree Node -----
class MUXTreeNode(object):
    def __init__(self, nodeId, fanin0id=-1, fanin1id=-1):
        self.nodeId = nodeId
        self.fanins = (fanin0id, fanin1id)
        self.level = -1
        self.iterId = 0
    
    def print(self):
        print("nodeId: %d; fanins: %s; level: %d" % (self.nodeId, self.fanins, self.level))

#----- MUX Tree Model -----
class MUXTree(object):
    def __init__(self, nInputs, bitAssign=None):
        self.nInputs = nInputs
        self.bitAssign = bitAssign
        self.nodes = []
        self.strash = dict()
        self.globalIterId = 0

        self.genFullTree(nInputs, bitAssign)

    def printNodes(self):
        for node in self.nodes:
            node.print()

    def printTree(self):
        print("Now print the MUX tree in dfs order")
        self.globalIterId += 1
        self.dfsPrintTree(self.rootId)

    def dfsPrintTree(self, nodeId):
        if nodeId == -1:
            return -1
        node = self.nodes[nodeId]
        if node.fanins[0] == -1: #Leaf node
            node.level = 0
            #return 0
        if node.iterId == self.globalIterId: #visited
            return node.level

        #set "visited" flag 
        node.iterId = self.globalIterId
        level0 = self.dfsPrintTree(node.fanins[0])
        level1 = self.dfsPrintTree(node.fanins[1])
        node.level = max(level0, level1) + 1
        node.print()
        return node.level
    
    def countNodes(self):
        print("Now count the nodes in the MUX tree")
        self.globalIterId += 1
        cnt = self.dfsCountNodes(self.rootId)
        return cnt

    #isC means the node is visited as fanin0
    #First calling will add PIs in self.strash, and counting PIs
    #other callings will not counting the PIs, while the other nodes are counted for only once
    def dfsCountNodes(self, nodeId, isC=True):
        #if nodeId == -1:
            #return 0
        node = self.nodes[nodeId]
        if node.fanins[0] == -1 and node.fanins[1] == -1: #Leaf node
            nodeInfo = (nodeId, isC)
            if nodeInfo in self.strash:
                return 0
            else:
                self.strash[nodeInfo] = nodeId
                return 1
        if node.iterId == self.globalIterId: #visited
            return 0

        #set "visited" flag 
        node.iterId = self.globalIterId
        count0 = self.dfsCountNodes(node.fanins[0], True)
        count1 = self.dfsCountNodes(node.fanins[1], False)
        return count0 + count1 + 1
        
    def genFullTree(self, k, bitAssign=None):
        #k is the nInputs of the dslut
        if bitAssign == None: 
            bitAssign = [x for x in range(2**k)]
        elif len(bitAssign) != 2**k:
                print("Error in MUXTree.genFullTree(): invalid input: bitAssign")
                exit()

        #initialize all the nodes
        nNodes = 2*(2**k - 1) + 1 #including the root node
        nodes = [MUXTreeNode(index) for index in range(nNodes)]

        #connect nodes except the nodes of level0
        #root occupies the additional level
        for level in range(k):
            curLevelStart = 2**(k + 1) - 2**(k + 1 - level)
            curLevelNumNode = 2**(k - level)

            nextLevelStart = 2**(k + 1) - 2**(k + 1 - level - 1)
            nextLevelNumNode = 2**(k - level - 1)

            for i in range(nextLevelNumNode):
                nodeId = nextLevelStart + i
                node = nodes[nodeId]
                faninId = curLevelStart + i * 2
                if level == 0:
                    node.fanins = (bitAssign[faninId], bitAssign[faninId + 1])
                else:
                    node.fanins = (faninId, faninId + 1)
            
        self.nNodes = nNodes
        self.nodes = nodes
        self.rootId = nNodes - 1
        self.printNodes()
        return nodes

    #This function is covered by dfsStrash
    def dfsFindSameFanin(self, nodeId):
        node = self.nodes[nodeId]
        if node.fanins[0] == -1: #Leaf node
            return node.nodeId
        if node.iterId == self.globalIterId: #visited
            return node.nodeId

        #set "visited" flag 
        node.iterId = self.globalIterId
        
        newFanin0 = self.dfsFindSameFanin(node.fanins[0])
        newFanin1 = self.dfsFindSameFanin(node.fanins[1])

        #Pending
        if newFanin0 > newFanin1:
            temp = newFanin0
            newFanin0 = newFanin1
            newFanin1 = temp

        node.fanins = (newFanin0, newFanin1)

        if node.fanins[0] == node.fanins[1]:
            print("delete nodes[%d] due to same fanin" % (node.nodeId))
            return node.fanins[0]
        return node.nodeId
        
    #Prune the muxtree by same-input and structure-hash    
    #isC means the node is visited as fanin0
    def dfsStrash(self, nodeId, isC=True):
        node = self.nodes[nodeId]
        if node.fanins[0] == -1: #Leaf node
            '''
            nodeInfo = (nodeId, isC)
            if nodeInfo not in self.strash:
                self.strash[nodeInfo] = nodeId
            '''
            return node.nodeId
        if node.iterId == self.globalIterId: #visited
            return node.nodeId

        #set "visited" flag 
        node.iterId = self.globalIterId

        #Assume the fanin0 is complemented
        newFanin0 = self.dfsStrash(node.fanins[0], True)
        newFanin1 = self.dfsStrash(node.fanins[1], False)
        nodeInfo = (newFanin0, newFanin1, isC)

        if newFanin0 == newFanin1:
            print("delete nodes[%d] due to same fanin" % (node.nodeId))
            #return node.fanins[0]
            return newFanin0
        if nodeInfo in self.strash:
            print("delete nodes[%d] due to strash" % (node.nodeId))
            return self.strash[nodeInfo]
        else:
            node.fanins = (newFanin0, newFanin1)
            self.strash[nodeInfo] = nodeId
            return nodeId

    def optimizeMuxTree(self):
        #count= self.countNodes()
        #print("Before opt, count: ", count)
        #self.printNodes()

        self.globalIterId += 1
        self.dfsStrash(self.rootId)
        #self.printNodes()

        #print("len(self.strash) = ", len(self.strash))
        #print("self.strash: ", self.strash)

        countNew = self.countNodes()
        print("countNew: ", countNew)

        print("len(self.strash) = ", len(self.strash))
        #print("self.strash: ", self.strash)

        #self.printTree()
        return countNew


#===========================================================================
#----- Testbench -----
if __name__ == "__main__":
    start = time.perf_counter()

    if False:
        #libFileName = "./dsdlib/dsdlibDump/lib_all_best.txt"
        libFileName = "./dsdlib/dsdlibDump/lib_all.txt"
        funcList = importLibFile(libFileName)
        #libFileName = "./dsdlib/dsdlibDump/lib_koios.txt"
        #funcList = importLibFile(libFileName)
        #libFileName = "./dsdlib/dsdlibDump/lib_vtr.txt"
        #funcList = importLibFile(libFileName)

    '''
    covers1 = [[1,3],[1,-3,4],[2,3,4]]
    tt1 = computeTtFromIsop(covers1, 4)
    print("tt1: ", tt1)
    covers2 = [[1,2],[1,-3,4],[2,3,4]]
    tt2 = computeTtFromIsop(covers2, 4)
    print("tt2: ", tt2)
        
    tt = [0,1,1,0]
    tt_cnf = [not x for x in tt] + tt
    ttv_cnf = tt2int(tt_cnf)
    clauses = genClausesFromTt(ttv_cnf, 3)
    print("clauses of {}: {}".format(tt, clauses))
    
    tt = [0,0,0,1]
    tt_cnf = [not x for x in tt] + tt
    ttv_cnf = tt2int(tt_cnf)
    clauses = genClausesFromTt(ttv_cnf, 3)
    print("clauses of {}: {}".format(tt, clauses))
    
    tt = [0,1,0,1,0,0,1,1]
    ttv = tt2int(tt)

    mux2 = LOGIC_Model(0, 3, ttv)
    mux2.varO = 1
    varList = [10,100,1000]
    mux2.assignFaninVarName(varList)
    mux2.genLocalCNFClauses()
    '''

    '''
    blifFile = "/home/ymc/project/abc_tb/titan_blif/denoise.blif"
    libFile = "/home/ymc/buffer/plb/dsdlib/libTitan.dsd"
    mrFile = "/home/ymc/buffer/plb/matchResult/MatchResult9inputTitan.txt"
    nLuts, lev = abcMapToLut(blifFile, 6)
    print("nLuts =", nLuts)
    print("lev =", lev)
    nLuts, lev = abcMapToDslut(blifFile, libFile, mrFile, 9)
    print("nLuts =", nLuts)
    print("lev =", lev)
    '''

    #import two libs
    if True:
        nInputs = 6
        libFileName = "./dsdlib/dsdlibDump/lib_all.txt"
        dslut_seeker = DSLUT_Seeker(nInputs, libFileName)
        #dslut_seeker.importMatchResult("./matchResult/mr_plb8_neo.txt")
        #dslut_seeker.importMatchResult("./matchResult/mr_dslut6_neo.txt", True)
        #dslut_seeker.importMatchResult("./dslut_res/dslut7_neo2/mr_dslut7_neo_alone.txt")
        #dslut_seeker.importMatchResult("./dslut_res/dslut7_neo2/mr_dslut7_neo_half.txt", True)
        #dslut_seeker.importMatchResult("./dslut_res/dslut7_neo2/mr_dslut7_neo_quarter.txt", True)
        #dslut_seeker.importMatchResult("./dslut_res/dslut6_koios/mr_dslut6_koios_libk_alone.txt")
        #dslut_seeker.importMatchResult("./dslut_res/dslut6_koios/mr_dslut6_koios_libk_half.txt", True)

        #compare two matchResults
        dslut_seeker.importMatchResult("./matchResult/mr_dslut6_koios.txt")
        dslut_seeker.importMatchResult("./matchResult/mr_dslut6_neo.txt", True)

        dslut_seeker.exportMatchResult()




    if False:
        #main test
        nInputs = 6
        libFileName = "./dsdlib/dsdlibDump/libKoiosBest.txt"
        #libFileName = "./dsdlib/dsdlibDump/lib_all_best.txt"
        #libFileName = "./dsdlib/libBase.txt"
        #libFileName = "./dsdlib/libBaseBest.txt"
        #libFileName = "./dsdlib/felut/lut2.txt"
        dslut_seeker = DSLUT_Seeker(nInputs, libFileName)
        dslut_seeker.seekDSLUT()
        #dslut_seeker.importMatchResult("MatchResult_Sep04_1442.txt")
        #dslut_seeker.exportMatchResult()
        #print("libFile:", libFileName)
    
        #LUT5+LUT2
        #pd = PlbDescription(PlbType.LUT_LOGIC)
        #pd.nInputsLut = 5
        if False:
            dslut_seeker.match(6, pd, dslut_seeker.funcList, 8, 1, 100000)
            dslut_seeker.exportMatchResult()
            
        if False:
            pd = PlbDescription(PlbType.FRAC_PLB_0)
            pd.bitAssign = [0, 1, 1, 14, 2, 2, 2, 13, 2, 3, 2, 4, 2, 5, 2, 5, 6, 2, 3, 4, 6, 2, 5, 5, 6, 5, 12, 4, 6, 5, 5, 5, 7, 8, 8, 8, 9, 10, 10, 9, 7, 0, 6, 10, 9, 0, 10, 0, 7, 8, 9, 10, 9, 10, 9, 9, 7, 11, 9, 10, 9, 9, 9, 0]
            pd.isCompList = [True, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False]
            pd.nBits =  14

            dslut_seeker.match(8, pd, dslut_seeker.funcList, 8, 1, 200000)
            dslut_seeker.exportMatchResult()
        if False:
            #pd = PlbDescription(PlbType.FRAC_PLB_0)
            #pd.bitAssign = [0, 1, 1, 14, 2, 2, 2, 13, 2, 3, 2, 4, 2, 5, 2, 5, 6, 2, 3, 4, 6, 2, 5, 5, 6, 5, 12, 4, 6, 5, 5, 5, 7, 8, 8, 8, 9, 10, 10, 9, 7, 0, 6, 10, 9, 0, 10, 0, 7, 8, 9, 10, 9, 10, 9, 9, 7, 11, 9, 10, 9, 9, 9, 0]
            #pd.isCompList = [True, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False]
            #pd.nBits =  14
            pd = PlbDescription(PlbType.FRAC_LUT6)
            dslut_seeker.match(nInputs, pd, dslut_seeker.funcList, 8, 1, 10000)
            dslut_seeker.exportMatchResult()

            #plb = PLB_Model(nInputs, pd)
            #covers = [[-1,-2,-3,-4,-5,-6,-7,-8]]
            #tt = computeTtFromIsop(covers, 8)
            #ttv = tt2int(tt)
            #res, resTt = plb.solveQBF(ttv, 8)
            


    '''
    #coverage analysis of a matched dsdlib
    nInputs = 8
    libFileName = "./dsdlib/felut/lut2lut2.txt"
    dslut_seeker = DSLUT_Seeker(nInputs, libFileName)
    dslut_seeker.exportMatchResult()
    print("libFile:", libFileName)
    '''

    


    '''
    #golden structure
    nInputs = 8
    pd = PlbDescription(PlbType.FRAC_PLB_0)    
    pd.bitAssign = [0, 1, 1, 14, 2, 2, 2, 13, 2, 3, 2, 4, 2, 5, 2, 5, 6, 2, 3, 4, 6, 2, 5, 5, 6, 5, 12, 4, 6, 5, 5, 5, 7, 8, 8, 8, 9, 10, 10, 9, 7, 0, 6, 10, 9, 0, 10, 0, 7, 8, 9, 10, 9, 10, 9, 9, 7, 11, 9, 10, 9, 9, 9, 0]
    pd.isCompList = [True, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False]
    pd.nBits =  14
    #dslut_seeker.match(nInputs, pd, dslut_seeker.funcList, 8, 1, 50000)
    #dslut_seeker.exportMatchResult()
    if True:
        plb = PLB_Model(nInputs, pd)
        covers = [[-1,-2,-3,-4,-5,-6,-7,-8]]
        tt = computeTtFromIsop(covers, 8)
        ttv = tt2int(tt)
        res, resTt = plb.solveQBF(ttv, 8)
    '''

    '''
    #optimize the muxtree
    #bitAssign = [0, 1, 1, 14, 2, 2, 2, 13, 2, 3, 2, 4, 2, 5, 2, 5, 6, 2, 3, 4, 6, 2, 5, 5, 6, 5, 12, 4, 6, 5, 5, 5, 7, 8, 8, 8, 9, 10, 10, 9, 7, 0, 6, 10, 9, 0, 10, 0, 7, 8, 9, 10, 9, 10, 9, 9, 7, 11, 9, 10, 9, 9, 9, 0]
    bitAssign = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 12, 8, 4, 17, 9, 16, 16, 17, 10, 8, 4, 17, 10, 16, 16, 18, 19, 19, 19, 20, 19, 19, 20, 18, 20, 19, 19, 20, 20, 19, 20, 18, 19, 20, 19, 20, 17, 20, 20, 18, 20, 20, 19, 20, 20, 20, 20]
    mt = MUXTree(6, bitAssign)
    mt.optimizeMuxTree()
    mt.printTree()
    '''



    '''
    #import dsdlibDump.txt
    funcList = importLibFile("dsd_lib_best.txt")
    print("nFuncsAll = ", len(funcList))
    funcListCutset = [func for func in funcList if func.nOccurCutset > 0]
    print("nFuncsCutset = ", len(funcListCutset))
    funcListBest = [func for func in funcList if func.nOccurBest > 0]
    print("nFuncsBest = ", len(funcListBest))
    print("nFuncsAll = ", len(funcList))
    funcsByNvars = []
    for i in range(1,10):
        funcs = [func for func in funcList if func.nSupp == i]
        funcsByNvars.append(funcs)

    nOccurByNvars = [0 for i in range(len(funcsByNvars))]
    for i in range(len(funcsByNvars)):
        funcs = funcsByNvars[i]
        for func in funcs:
            nOccurByNvars[i] += func.nOccurBest
    nOccurSum = 0
    for i in nOccurByNvars:
        nOccurSum += i

    for i in range(9):
        print("nSupp = ", i+1, " nFuncs = ", len(funcsByNvars[i]), "\tnOccurs = ", nOccurByNvars[i], "\tpercent = ", 100.0*nOccurByNvars[i]/nOccurSum)

    #funcListSorted = sorted(funcList, key=lambda func: -1*func.nOccurNormal)
    '''

    
    #Different PLB Models
    if False:
        k = 6
        #plb = PLB_Model(6) #SINGLE_LUT
        pd = PlbDescription(PlbType.LUT_LOGIC)
        pd.nInputsLut = k - 1
        #pd = PlbDescription()
        #golden dslut6
        #pd.bitAssign = [0, 1, 1, 14, 2, 2, 2, 13, 2, 3, 2, 4, 2, 5, 2, 5, 6, 2, 3, 4, 6, 2, 5, 5, 6, 5, 12, 4, 6, 5, 5, 5, 7, 8, 8, 8, 9, 10, 10, 9, 7, 0, 6, 10, 9, 0, 10, 0, 7, 8, 9, 10, 9, 10, 9, 9, 7, 11, 9, 10, 9, 9, 9, 0]
        #pd.isCompList = [True, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False, False]
        #pd.nBits =  14
        #pd.nBits = 2**k
        #pd.bitAssign = [i+1 for i in range(2**k)]
        #pd.isCompList = [False for i in range(2**k)]
        plb = PLB_Model(k, pd)
        #plb = PLB_Model(k)
        
        for i in range(1):
            #tt_value = randint(0,2**(2**(k-1))-1)
            tt_value = 27
            tt = int2tt(tt_value, k)
            covers, _ = computeIsop(tt, tt, k)
            print(covers)
            
            #tt = int2tt(tt_value, k - 1)
            #tt_and = [False, False, False, True]
            #tt_plb = composeTwoFuncs(tt, k-1, tt_and, 2, 4)
            #tt_value = tt2int(tt_plb)
            
            res, resTtValue = plb.solveQBF(tt_value, k, 50000)
            print("funcTtv: ", tt_value)
            print("plbTtv: ", resTtValue)
            print("i: ", i)
    


    '''
    #Func Composition
    ttv_out = 202
    nVars_out = 3
    tt_out = int2tt(ttv_out, nVars_out)
    ttv_in = 8
    nVars_in = 2
    tt_in = int2tt(ttv_in, nVars_in)
    ttv_in_2 = 1
    nVars_in_2 = 2
    tt_in_2 = int2tt(ttv_in_2, nVars_in_2)
    resTt = composeTwoFuncs(tt_out, nVars_out, tt_in, nVars_in, 1)
    resnVars = nVars_out + nVars_in - 1
    resTt = composeTwoFuncs(resTt, resnVars, tt_in_2, nVars_in_2, 0)
    '''

    
    '''
    #CNF Model
    tt = [1,0,1,0,1,0,0,1]
    clauses = genClausesFromTt(tt2int(tt), 3)
    print("clauses = ", clauses)

    k = 4
    m = DSLUT_Model(0,k,2**k,[i+1 for i in range(2**k)],[False for i in range(2**k)]) 
    varBaseI = m.nVarsGlobal + 1
    for i in range(m.nFanins):
        m.varI[i] = varBaseI + i
    m.varO = varBaseI + m.nFanins
    varBase = m.varO + 1
    
    m.genLocalCNFClauses(varBase)
    '''
    
    '''
    #ISOP
    tt = int2tt(0xE0)
    covers, restt = computeIsop(tt, tt, 3)
    print("covers = ", covers)
    print("restt = ", restt)
    ttres = computeTtFromIsop(covers, 3)
    print("ttres = ", ttres)
    
    for i in range(128):
        tt = int2tt(i, 4)
        print("i = ", i)
        covers, restt = computeIsop(tt, tt, 4)
        print("covers = ", covers)
        print("restt = ", restt)
        tt1 = computeTtFromIsop(covers, 4)
        print("tt_value = ", tt2int(tt1))
    
    tt = int2tt(0b00010111)
    covers, restt = computeIsop(tt, tt, 3)
    print("covers = ", covers)
    print("restt = ", restt)
    covers_mux2 = [[-3, 1], [3, 2]]
    tt_mux2 = computeTtFromIsop(covers_mux2, 3)
    ttv = tt2int(tt_mux2)
    covers, _ = computeIsop(tt_mux2, tt_mux2, 3)
    print("MUX2:\n", covers, "\n", ttv)
    covers_mux4 = [[1, -5, -6], [2, 5, -6], [3, -5, 6], [4, 5, 6]]
    tt_mux4 = computeTtFromIsop(covers_mux4, 6)
    ttv = tt2int(tt_mux4)
    covers, _ = computeIsop(tt_mux4, tt_mux4, 6)
    print("MUX4:\n", covers, "\n", hex(ttv))

    ttv = int("0123456789ABCDEF", 16)
    tt = int2tt(ttv, 6)
    covers, _ = computeIsop(tt, tt, 6)
    print(covers)
    '''

    
    
    #NPN
    #tt = int2tt(112,3)
    #tt2int(tt)
    #c0,c1 = computeCofactors(int2tt(142),1)
    #tt = mergeCofactors(c0, c1, 0)
    #tt = int2tt(142)
    #tt1 = negateOneInput(tt, 2)
    #tt2 = negateOneInput(tt1, 2)
    
    #tt = int2tt(248)
    #tt1 = moveInput(tt, 2, 1)
    #tt_value = int("F8", 16)
    #tt = int2tt(tt_value, 3)
    #print(tt)
    #tt2 = swapTwoInput(tt, 1, 2)
    #print(tt2)

    
    #tt = int2tt(8, 2)
    #enumAllInputNegation(tt, 2)
    
    #tt = int2tt(3)
    #result = enumAllInputPermutation(tt, 2)
    #print(result)
    
    '''
    equals = computeNPNbyEnum(24, 3)
    print("len(equals) = ", len(equals))
    print("min(equals) = ", min(equals))
    print("equals = ", equals)
    print(int2tt(min(equals), 3))

    analyzeAllFunc(3)
    '''
    
    end = time.perf_counter()
    print("Running time: %s Seconds"  % (end-start))


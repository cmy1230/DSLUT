import os
import re
import time
import platform
import lxml.etree as et
from multiprocessing import Pool

from prepack import prepack
from prepack import opt_const

localtime = time.asctime(time.localtime(time.time()))
print("Local time :", localtime)
curOs = platform.system()
print("Current OS: ", curOs)
if curOs == "Linux":
    flagLinux = True
elif curOs == "Windows":
    flagLinux = False
else:
    print("Unknown system")
    exit()

def genDsdlib(srcPath, outputPath=".", K=9):
    if os.path.isdir(outputPath):
        print(outputPath, "exists.")
    else:
        os.mkdir(outputPath)
        print(outputPath, "is newly created.")
    
    targetFiles = []
    for path,dirs,files in os.walk(srcPath):
        for fi in files:
            netlistName, fileExt = os.path.splitext(fi)
            if fileExt == '.blif':
                targetFiles.append(os.path.join(srcPath, fi))
    #print(targetFiles)
    scriptFile = os.path.join(outputPath, "genlib.script")
    with open(scriptFile, "w") as f:
        for target in targetFiles:
            line = "read %s; if -n -K %d; strash; dc2; if -n -K %d;\n" \
                % (target, K, K)
            f.write(line)
        line = "\ndsd_save %s%d.dsd\n" % (os.path.join(outputPath, "lib"), K)
        f.write(line)
    
    cmd = "abc -f %s" % (scriptFile)
    print(cmd)
    if flagLinux:
        os.system(cmd)


def runOdin(srcFile, archFile, configTemplateFile, outputPath="."):
    path, fileName = os.path.split(srcFile)
    netlistName, fileExt = os.path.splitext(fileName)
    if fileExt == '':
        fileName = fileName + '.v'
    elif fileExt != '.v':
        print("Error in runOdin(): invalid file extension: %s" % (fileName))
        exit()

    if os.path.isdir(outputPath):
        print(outputPath, "exists.")
    else:
        os.mkdir(outputPath)
        print(outputPath, "is newly created.")
    
    resFile = os.path.join(outputPath, "%s.odin.blif" % (netlistName))
    configFile = os.path.join(outputPath, "config.xml")
    logFile = os.path.join(outputPath, "odin.out")

    tree = et.parse(configTemplateFile)
    root = tree.getroot()
    root.find(".//input_path_and_name").text = srcFile
    root.find(".//output_path_and_name").text = resFile
    root.find(".//arch_file").text = archFile
    tree.write(configFile)

    cmd = "odin_II -c %s > %s" % (configFile, logFile)
    print(cmd)
    if flagLinux:
        os.system(cmd)
    print("Odin finished!")
    return resFile

def runAbc(srcFile, restoreClkScript, K):
    outputPath, fileName = os.path.split(srcFile)
    tmplist = fileName.split('.')
    if tmplist[-1] != 'blif':
        print("Error in runAbc(): invalid file extension: %s" % (fileName))
        exit()
    netlistName = tmplist[0]

    abcNoClkFile = os.path.join(outputPath, "%s.abc_noclk.blif" % (netlistName))
    logFile = os.path.join(outputPath, "abc.out")
    resFile = os.path.join(outputPath, "%s.pre-vpr.blif" % (netlistName))
    
    abcCmd = "read %s; strash; ifraig -v; dc2 -v; dch -f; if -K %d -v; mfs2 -v; print_stats; write_hie %s %s" \
        % (srcFile, K, srcFile, abcNoClkFile)
    cmd = '/home/ymc/project/abc_baseline/abc -c "%s" > %s' % (abcCmd, logFile)
    print(cmd)
    if flagLinux:
        os.system(cmd)

    abcNoClkPrepackFile = os.path.join(outputPath, "%s.abc_noclk.prepack.blif" % (netlistName))
    runPrepack(abcNoClkFile, abcNoClkPrepackFile)

    cmd = '%s %s %s %s' % (restoreClkScript, srcFile, abcNoClkPrepackFile, resFile)
    print(cmd)
    if flagLinux:
        os.system(cmd)
    
    print("Abc finished!")
    return resFile

def runAbcDslut(srcFile, libFile, matchResFile, restoreClkScript, K, outputPath=".", fPrepack=True):
    _, fileName = os.path.split(srcFile)
    tmplist = fileName.split('.')
    if tmplist[-1] != 'blif':
        print("Error in runAbc(): invalid file extension: %s" % (fileName))
        exit()
    if tmplist[-2] == 'odin':
        netlistName = fileName[:-10]
    else:
        netlistName = fileName[:-5]

    if os.path.isdir(outputPath):
        print(outputPath, "exists.")
    else:
        os.mkdir(outputPath)
        print(outputPath, "is newly created.")

    abcNoClkFile = os.path.join(outputPath, "%s.abc_noclk.blif" % (netlistName))
    logFile = os.path.join(outputPath, "abc.out")
    resFile = os.path.join(outputPath, "%s.pre-vpr.blif" % (netlistName))
    
    #abcCmd = "dsd_load %s; import_match_result %s; read %s; strash; ifraig -v; dc2 -v; dch -f; if -k -K %d -v; print_stats; write_hie %s %s" \
    #abcCmd = "dsd_load %s; import_match_result %s; read %s; strash; ifraig -v; dc2 -v; dch -f; if -k -K %d -v; mfs2 -a -v; print_stats; write_hie %s %s" \
    abcCmd = "dsd_load %s; import_match_result %s; read %s; strash; ifraig -v; dc2 -v; dch -f; if -k -C 16 -K %d -v; mfs2 -a -v; print_stats; write_hie %s %s" \
        % (libFile, matchResFile, srcFile, K, srcFile, abcNoClkFile)
    cmd = '/home/ymc/project/abc_homo_dslut6/abc -c "%s" > %s' % (abcCmd, logFile)
    print(cmd)
    if flagLinux:
        os.system(cmd)

    if fPrepack:
        dslutDef = "#define subckt dslut6 in[0] in[1] in[2] in[3] in[4] in[5] out[0]"
    else:
        dslutDef = None
    abcNoClkPrepackFile = os.path.join(outputPath, "%s.abc_noclk.prepack.blif" % (netlistName))
    runPrepack(abcNoClkFile, abcNoClkPrepackFile, dslutDef)

    #cmd = '%s %s %s %s' % (restoreClkScript, srcFile, abcNoClkFile, resFile)
    cmd = '%s %s %s %s' % (restoreClkScript, srcFile, abcNoClkPrepackFile, resFile)
    print(cmd)
    if flagLinux:
        os.system(cmd)
    
    print("Abc finished!")
    return resFile
    

def runVpr(srcFile, archFile, chanWidth):
    outputPath, fileName = os.path.split(srcFile)
    tmplist = fileName.split('.')
    if tmplist[-1] != 'blif':
        print("Error in runVpr(): invalid file extension: %s" % (fileName))
        exit()
    if tmplist[-2] == 'pre-vpr':
        netlistName = fileName[:-13]
    else:
        netlistName = fileName[:-5]
    logFile = "vpr.out" #% (netlistName)

    cmd = "cd %s; vpr %s %s --circuit_file %s --route_chan_width %d > %s" \
        % (outputPath, archFile, netlistName, fileName, chanWidth, logFile)
    print(cmd)
    if flagLinux:
        os.system(cmd)
    print("Vpr finished!")
    
class ResData(object):
    def __init__(self, netlistName, abcNplb=0, abcLev=0, vprDelay=0, vprAreaRouting=0, vprAreaClb=0, vprNclb=0, flowRuntime=0):
        self.netlistName = netlistName
        self.abcNplb = abcNplb
        self.abcLev = abcLev
        self.vprDelay = vprDelay
        self.vprAreaClb = vprAreaClb
        self.vprAreaRouting = vprAreaRouting
        self.vprNclb = vprNclb
        self.flowRuntime = flowRuntime
        self.chanWidth = 0
        self.odinRuntime = 0
        self.abcRuntime = 0
        self.vprRuntime = 0
    
    def print(self):
        print("\n====================\n")
        print("netlistName: ", self.netlistName)
        print("abcNplb: ", self.abcNplb)
        print("abcLev: ", self.abcLev)
        print("vprDelay: ", self.vprDelay)
        print("vprAreaRouting: ", self.vprAreaRouting)
        print("vprAreaClb: ", self.vprAreaClb)
        print("vprNclb: ", self.vprNclb)
        print("chanWidth: ", self.chanWidth)
        print("odinRuntime: ", self.odinRuntime)
        print("abcRuntime: ", self.abcRuntime)
        print("vprRuntime: ", self.vprRuntime)
        print("flowRuntime: ", self.flowRuntime)
    
class VtrFlow(object):
    def __init__(self, archFile, configTemplate, restoreClkScript, libFile=None, matchResFile=None, K=6, chanWidth=300):
        self.archFile = archFile
        self.configTemplate = configTemplate
        self.restoreClkScript = restoreClkScript
        self.libFile = libFile
        self.matchResFile = matchResFile
        self.K = K
        self.chanWidth = chanWidth
        
    def runOne(self, srcFile, outputPath='.'): #srcFile.v
        print("Now in runOne()")
        odinResFile = runOdin(srcFile, self.archFile, self.configTemplate, outputPath)
        abcResFile = runAbc(odinResFile, self.restoreClkScript, self.K)
        runVpr(abcResFile, self.archFile, self.chanWidth)
        print("%s is done" % (srcFile))
        '''
        cmd = "cd %s; rm *.rpt *.log *.net* *.place *.route" % (outputPath)
        print(cmd)
        if flagLinux:
            os.system(cmd)
        '''
    
    def runOne4Dslut(self, srcFile, outputPath='.'): #srcFile.odin.blif
        print("Now in runOne4Dslut()")
        abcResFile = runAbcDslut(srcFile, self.libFile, self.matchResFile, self.restoreClkScript, self.K, outputPath, False)
        runVpr(abcResFile, self.archFile, self.chanWidth)
        print("%s is done" % (srcFile))
        '''
        cmd = "cd %s; rm *.rpt *.log *.net* *.place *.route" % (outputPath)
        print(cmd)
        if flagLinux:
            os.system(cmd)
        '''

    def runSrcPath(self, srcPath, outputPath="."):
        print("Now in runSrcPath()")
        print("srcPath: ", srcPath)

        #parameters for Pool
        flagPool = True
        nProcs = 40
        chunksize = 1

        if os.path.isdir(outputPath):
            print(outputPath, "exists.")
        else:
            os.mkdir(outputPath)
            print(outputPath, "is newly created.")

        targetFiles = []
        for path,dirs,files in os.walk(srcPath):
            for fi in files:
                netlistName, fileExt = os.path.splitext(fi)
                if fileExt == '.v':
                    targetFiles.append(os.path.join(srcPath, fi))
                if fileExt == '.blif':
                    targetFiles.append(os.path.join(srcPath, fi))

        print("targetFiles: ", targetFiles)
        worker = WorkerFactory(self, outputPath)
        
        if flagPool:
            with Pool(processes = nProcs) as pool:
                pool.map(worker, targetFiles, chunksize)
        else:
            for srcFile in targetFiles:
                worker(srcFile)

    def parseResult(self, resPath, outputPath='.', flagOdin=True, surfix=None):
        print("Now in parseResult()")
        if os.path.isdir(outputPath):
            print(outputPath, "exists.")
        else:
            os.mkdir(outputPath)
            print(outputPath, "is newly created.")
        if flagOdin:
            resBlifPath = os.path.join(outputPath, "odinBlif")
            if os.path.isdir(resBlifPath):
                print(resBlifPath, "exists.")
            else:
                os.mkdir(resBlifPath)
                print(resBlifPath, "is newly created.")

        targetNetlists = []
        for path,dirs,files in os.walk(resPath):
            for dir in dirs:
                targetNetlists.append(dir)

        resDataMap = dict() 
        for netlist in targetNetlists:
            targetPath = os.path.join(resPath, netlist)
            parseData = ResData(netlist)
            
            if flagOdin:
                cmd = "mv %s/*.odin.blif %s/%s.odin.blif" \
                    % (targetPath, resBlifPath, netlist)
                print(cmd)
                if flagLinux:
                    os.system(cmd)
    
                with open(os.path.join(targetPath, "odin.out")) as f:
                    line = f.readline()
                    while line:
                        searchObj = re.search(r'Odin II took (\S+) seconds', line)
                        if searchObj:
                            #print("odinRuntime = ", searchObj.group(1))
                            parseData.odinRuntime = float(searchObj.group(1))
                            break
                        line = f.readline()
            
            with open(os.path.join(targetPath, "abc.out")) as f:
                line = f.readline()
                while line:
                    searchObj = re.search(r'\s+nd\s*=\s*(\d+).*lev\s*=\s*(\d+)', line)
                    if searchObj:
                        #print("nd = ", searchObj.group(1))
                        parseData.abcNplb = int(searchObj.group(1))
                        #print("lev = ", searchObj.group(2))
                        parseData.abcLev = int(searchObj.group(2))
                        line = f.readline()
                        continue
                    searchObj = re.search(r'total time used: (\S*)', line)
                    if searchObj:
                        #print("abcRuntime = ", searchObj.group(1))
                        parseData.abcRuntime = float(searchObj.group(1))
                        break
                    line = f.readline()

            with open(os.path.join(targetPath, "vpr.out")) as f:
                line = f.readline()
                flagVprSuccess = False
                while line:
                    searchObj = re.search(r'Netlist clb blocks: (\d+)', line)
                    if searchObj:
                        #print("vprNclb = ", searchObj.group(1))
                        parseData.vprNclb = int(searchObj.group(1))
                        line = f.readline()
                        continue
                    searchObj = re.search(r'Total used logic block area: (\S+)', line)
                    if searchObj:
                        #print("vprAreaClb = ", searchObj.group(1))
                        parseData.vprAreaClb = searchObj.group(1)
                        line = f.readline()
                        continue
                    searchObj = re.search(r'Total routing area: (\S+),', line)
                    if searchObj:
                        #print("vprAreaRouting = ", searchObj.group(1))
                        parseData.vprAreaRouting = searchObj.group(1)
                        line = f.readline()
                        continue
                    searchObj = re.search(r'Final geomean non-virtual intra-domain period: (\S+) ns', line)
                    if searchObj:
                        #print("vprDelay = ", searchObj.group(1))
                        parseData.vprDelay = float(searchObj.group(1))
                        line = f.readline()
                        continue
                    searchObj = re.search(r'Circuit successfully routed with a channel width factor of (\S+).', line)
                    if searchObj:
                        #print("vprDelay = ", searchObj.group(1))
                        parseData.chanWidth = int(searchObj.group(1))
                        line = f.readline()
                        continue
                    searchObj = re.search(r'VPR succeeded', line)
                    if searchObj:
                        #print(line)
                        flagVprSuccess = True
                        line = f.readline()
                        continue
                    searchObj = re.search(r'The entire flow of VPR took (\S+) seconds', line)
                    if searchObj:
                        #print("vprRuntime = ", searchObj.group(1))
                        parseData.vprRuntime = float(searchObj.group(1))
                        break
                    line = f.readline()
                if not flagVprSuccess:
                    print("%s VPR Failed!!!!" % (parseData.netlistName))
                parseData.flowRuntime = parseData.odinRuntime + parseData.abcRuntime + parseData.vprRuntime
                #print("Flow runtime: ", parseData.flowRuntime)
            
            resDataMap[parseData.netlistName] = parseData
        
        #for key in resDataMap:
            #resDataMap[key].print()
        
        orderSeq = sorted(resDataMap, key=lambda x:x.lower())
        
        if surfix:
            csvFile = os.path.join(outputPath, "res%s.csv" % (surfix))
        else:
            csvFile = os.path.join(outputPath, "res.csv")
        with open(csvFile, 'w') as f:
            f.write("netlist, abcNplb, abcLev, vprDelay, vprAreaClb, vprAreaRouting, vprNclb, chanWidth, odintime, abctime, vprtime, flowtime\n")
            for key in orderSeq:
                d = resDataMap[key]
                line = "%s, %d, %d, %f, %s, %s, %d, %d, %f, %f, %f, %f\n" \
                    % (d.netlistName, d.abcNplb, d.abcLev, d.vprDelay, d.vprAreaClb, d.vprAreaRouting, d.vprNclb, d.chanWidth, d.odinRuntime, d.abcRuntime, d.vprRuntime, d.flowRuntime)
                f.write(line)
            

class WorkerFactory(object):
    def __init__(self, flow, outputPath):
        self.flow = flow
        self.outputPath = outputPath
        
    def __call__(self, srcFile):
        start = time.perf_counter()
        _, fileName = os.path.split(srcFile)
        tmplist = fileName.split('.')
        if tmplist[-1] == 'v':
            netlistName = fileName[:-2]
            self.flow.runOne(srcFile, os.path.join(self.outputPath, netlistName))
        elif tmplist[-1] == 'blif':
            if tmplist[-2] == 'odin':
                netlistName = fileName[:-10]
            else:
                netlistName = fileName[:-5]
            self.flow.runOne4Dslut(srcFile, os.path.join(self.outputPath, netlistName))
        else:
            print("Error in worker(): invalid file extention: %s" % (tmplist[-1]))
            exit()
        end = time.perf_counter()
        print("Flow for %s runtime: %s Seconds"  % (srcFile, end-start))
    

#Calling prepack flow from prepack.py
def runPrepack(srcFile, resFile, dslutDef=None):
    tmpFile = srcFile + '.prepack.tmp'
    netlist = prepack.BlifCircuit(srcFile, dslutDef)
    netlist.printInputDistribution()
    if dslutDef:
        netlist.balanceSortedLogicUsageLazy()
        netlist.writeBlif(tmpFile)
        opt_const.optConst(tmpFile, resFile)
    else:
        netlist.writeBlif(resFile)
    return


#===========================================================================
#----- Testbench -----
if __name__ == "__main__":
    start = time.perf_counter()
    print("Now in vtrFlow.py")

    if flagLinux:
        vtrFlowPath = "/home/ymc/buffer/vtr_flow"
        outputPath = "/home/ymc/buffer/flow/fdslut/fdslut_normal"
        configFile = vtrFlowPath + "/config/odin_config.xml"
        parseOutputPath = "/home/ymc/buffer/flow/parseRes"
        #logFile = "/home/ymc/buffer/flow/flowBaselineArch.log"
    else:
        vtrFlowPath = "."
        outputPath = "result"
        configFile = "odin_config.xml"
        parseOutputPath = "."
        #logFile = "result/flowBaselineArch.log"
    #srcPath = vtrFlowPath + "/benchmark/baseline"
    archFile = vtrFlowPath + "/arch/target/fdslut/fdslut_normal.xml"
    restoreClkScript = vtrFlowPath + "/scripts/restore_multiclock_latch.pl"

    blifPath = vtrFlowPath + "/benchmark/blif/base"
    blifFile = blifPath + "/bnn.odin.blif"
    libFile = "/home/ymc/buffer/plb/dsdlib/libBase.dsd"
    matchResFile = "/home/ymc/buffer/plb/matchResult/mr_dslut6_plb8.txt"
    #matchResFile = "all"


    flow = VtrFlow(archFile, configFile, restoreClkScript, libFile, matchResFile, 9)
    #flow = VtrFlow(archFile, configFile, restoreClkScript)
    flow.runOne4Dslut(blifFile, outputPath)
    #flow.runOne(srcFile, outputPath)
    #flow.runSrcPath(blifPath, outputPath)
    #flow.parseResult(outputPath, parseOutputPath, False, "fdslut_normal")
    #genDsdlib(srcPath)







    end = time.perf_counter()
    print("Running time: %s Seconds"  % (end-start))

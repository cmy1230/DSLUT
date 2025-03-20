
import os
import re
import time
import platform
from vtrFlowHomo import VtrFlow

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

#----- Testbench -----
if __name__ == "__main__":
    start = time.perf_counter()

    if flagLinux:
        vtrFlowPath = "/home/ymc/buffer/vtr_flow"
        #outputPath = "/home/ymc/buffer/flow/fdslut"
        #outputPath = "/home/ymc/buffer/flow/dslut/homo_dslut7_area_autoCW_k8"
        outputPath = "/home/ymc/buffer/flow/dslut/homo_dslut6_koios_autoCW"
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
    #archFile = vtrFlowPath + "/arch/baseline/baselineHomoDslut7_mod.xml" #lut5mode and new rlut7 delay
    archFile = vtrFlowPath + "/arch/baseline/baselineHomoDslut6.xml"
    restoreClkScript = vtrFlowPath + "/scripts/restore_multiclock_latch.pl"

    blifPath = "/home/ymc/buffer/flow/baseline/odinBlifHomoLut6"
    #blifPath = "/home/ymc/buffer/flow/baseline/vtr"
    #blifPath = "/home/ymc/buffer/flow/baseline/koios"
    #blifFile = blifPath + "/bnn.odin.blif"
    #libFile = "/home/ymc/buffer/plb/dsdlib/libBase.dsd"
    libFile = "/home/ymc/buffer/plb/dsdlib/lib_all.dsd"
    matchResFile = "/home/ymc/buffer/plb/matchResult/mr_dslut6_koios.txt"
    #matchResFile = "all"


    #flow = VtrFlow(archFile, configFile, restoreClkScript)
    #flow = VtrFlow(archFile, configFile, restoreClkScript, libFile, matchResFile, 9)
    flow = VtrFlow(archFile, configFile, restoreClkScript, libFile, matchResFile, 6)
    flow.chanWidth = -1
    #flow.runOne(srcFile, outputPath)
    #flow.runOne4Dslut(blifFile, outputPath)
    flow.runSrcPath(blifPath, outputPath)
    flow.parseResult(outputPath, parseOutputPath, False, "homo_dslut6_koios_autoCW")
    #genDsdlib(srcPath)

    end = time.perf_counter()
    print("Running time: %s Seconds"  % (end-start))

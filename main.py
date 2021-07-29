import sys
import os

from llvmlite import binding as llvm

from analysis import setupBlocks, processLoops, processBranches, parseLoops, parseSrets
from vc import VC
from synthesis import synthesize, toSMT

if __name__ == "__main__":
  if len(sys.argv) < 6:
    raise Exception("usage: main.py <.ll or .bc file> <inv and ps file> <output file> <function name to parse> [loops info] [path to cvc4]")

  filename = sys.argv[1]
  basename = os.path.splitext(os.path.basename(filename))[0]
  ansFile = sys.argv[2]
  outFile = sys.argv[3]
  fnName = sys.argv[4]
  loopsFile = sys.argv[5] if len(sys.argv) > 5 else None
  cvcPath = sys.argv[6] if len(sys.argv) > 6 else None
  mode = "r" if filename.endswith(".ll") else "rb"
  with open(filename, mode=mode) as file:
    if filename.endswith(".ll"):
      ref = llvm.parse_assembly(file.read())
    elif filename.endswith(".bc"):
      ref = llvm.parse_bitcode(file.read())
    else:
      raise Exception("Unknown file type: %s" % filename)

    fn = ref.get_function(fnName)
    blocksMap = setupBlocks(fn.blocks)

    parseSrets(list(fn.arguments), blocksMap.values())

    loops = parseLoops(loopsFile, fnName) if loopsFile else None
    for l in loops:
      # assume for now there is only one header block
      if len(l.header) > 1: raise Exception("multiple loop headers: %s" % l)
      processLoops(blocksMap[l.header[0]], [blocksMap[n] for n in l.body],
                   [blocksMap[n] for n in l.exits], [blocksMap[n] for n in l.latches],
                   list(fn.arguments))

    # example for while4.c
    # processLoops(blocksMap["bb2"], [], [blocksMap[n] for n in ["bb2"]], [blocksMap[n] for n in ["bb5"]],
    #              list(fn.arguments))

    processBranches(blocksMap, list(fn.arguments))

    print("====== after transforms")
    for b in blocksMap.values():
      print("blk: %s" % b.name)
      for i in b.instructions:
        print("%s" % i)

    print("====== compute vc")
    (vars, invAndPs, preds, vc) = VC().computeVC(blocksMap, list(fn.blocks)[0].name, list(fn.arguments))

    if cvcPath:
      print("====== synthesis")
      synthesize(invAndPs, vars, invAndPs, vc, ansFile, cvcPath, basename)
    else:
      print("====== print to SMT file: %s" % outFile)
      toSMT(open(ansFile, mode="r").read(), vars, invAndPs, vc, outFile, False)


    # codegen -- NYI

import sys

from llvmlite import binding as llvm

from analysis import setupBlocks, processLoops, processBranches, parseLoops
from vc import VC

if __name__ == "__main__":
  if len(sys.argv) < 5:
    raise Exception("usage: main.py <.ll or .bc file> <inv and ps file> <output file> <function name to parse> [loops info]")

  filename = sys.argv[1]
  ansFilename = sys.argv[2]
  outFile = sys.argv[3]
  fnName = sys.argv[4]
  loopsFile = sys.argv[5] if len(sys.argv) > 5 else None

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

    loops = parseLoops(loopsFile, fnName) if loopsFile else None
    for l in loops:
      # assume for now there is only one header block
      if len(l.header) > 1: raise Exception("multiple loop headers: %s" % l)
      processLoops(blocksMap[l.header[0]], [blocksMap[n] for n in l.body],
                   [blocksMap[n] for n in l.exits], [blocksMap[n] for n in l.latches],
                   list(fn.arguments))

    # while 4.c
    # processLoops(blocksMap["bb2"], [], [blocksMap[n] for n in ["bb2"]], [blocksMap[n] for n in ["bb5"]],
    #              list(fn.arguments))

    processBranches(blocksMap, list(fn.arguments))

    print("====== after transforms")
    for b in blocksMap.values():
      print("blk: %s" % b.name)
      for i in b.instructions:
        print("%s" % i)

    print("====== compute vc")
    (varDecls, predDecls, vc) = VC().computeVC(blocksMap, list(fn.blocks)[0].name, list(fn.arguments))
    v = "\n".join(["(declare-const %s %s)" % (v.args[0], v.type) for v in varDecls])  # name and type
    # name, args, return type
    p = "\n".join(["(define-fun %s (%s) (%s) )" % (p.args[0],
                                                   " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]),
                                                   p.type)
                                                   for p in predDecls])

    # print the whole thing
    print("%s\n" % v)
    print("%s\n" % p)
    print("%s\n" % vc)
    print("(check-sat)\n(get-model)")

    with open(outFile, mode="w") as out, open(ansFilename, mode="r") as ans:
      noPSInv = filter(lambda p: p.args[0] != "ps" and not p.args[0].startswith("inv"), predDecls)
      pNoPSInv = "\n".join(["(define-fun %s (%s) (%s) )" % (p.args[0],
                                                         " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]),
                                                         p.type)
                         for p in noPSInv])
      out.write("%s\n\n%s\n\n%s\n\n%s\n\n(check-sat)\n(get-model)" % (ans.read(), v, pNoPSInv, vc))

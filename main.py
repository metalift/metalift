import sys

from llvmlite import binding as llvm

from analysis import setupBlocks
from vc import VC

if __name__ == "__main__":
  if len(sys.argv) < 3:
    raise Exception("usage: main.py <.ll or .bc file> <function name to parse>")

  filename = sys.argv[1]
  fnName = sys.argv[2]

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
    print("%s" % blocksMap)

    (varDecls, predDecls, vc) = VC().computeVC(blocksMap, list(fn.blocks)[0].name, list(fn.arguments))

    # print to smt
    v = "\n".join(["(declare-const %s %s)" % (v.args[0], v.args[1]) for v in varDecls])
    # predicate defs - name, args, and return type
    p = "\n".join(["(define-fun %s (%s) (%s) )" % (p.args[0],
                                                   " ".join("(%s %s)" % (a.args[0], a.args[1]) for a in p.args[1:-1]),
                                                   p.args[-1])
                                                   for p in predDecls])
    print("vars: %s" % v)
    print("preds: %s" % p)
    print("vc: %s" % vc)

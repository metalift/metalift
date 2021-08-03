import re
from collections import namedtuple

from ir import MLInst, Type
from vc import Block

def setupBlocks(blks):
  bbs = dict((b.name, Block(b.name, list(b.instructions))) for b in blks)

  for b in bbs.values():
    i = b.instructions[-1]
    opcode = i.opcode
    ops = list(i.operands)

    if opcode == "br":
      targets = ops[0:] if len(ops) == 1 else ops[1:]
    elif opcode == "switch":
      targets = ops[1::2]
    elif opcode == "ret":
      targets = []
    else: raise Exception("Unknown end block inst: %s" % i)

    b.succs = [bbs[t.name] for t in targets]

    for t in targets:
      bbs[t.name].preds.append(b)

  return bbs

# replace ret void with ret sret argument if srets are used
def parseSrets(fnArgs, blks):
  sret = None
  for a in fnArgs:
    if b"sret" in a.attributes:
      if sret is None: sret = a
      else: raise Exception("multiple sret arguments: %s and %s" % (sret, a))

  if sret:
    for b in blks:
      if b.instructions[-1].opcode == "ret":
        ops = list(b.instructions[-1].operands)
        if len(ops): raise Exception("return val not void: %s" % b.instructions[-1])
        else: b.instructions[-1] = MLInst.Return(sret)

# previous attempt in rewriting all STL vector fn calls
# def lowerVectorCalls(blks):
#   for b in blks:
#     for i in range(len(b.instructions)):
#       inst = b.instructions[i]
#
#       if inst.opcode == "call":
#         ops = list(inst.operands)
#         fnName = ops[-1].name
#         if fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev":
#           newInst = MLInstruction("call", "newlist")
#           newInst.name = ops[0].name
#           newInst.type = ops[0].type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv":
#           newInst = MLInstruction("call", ops[0], "listLength")
#           newInst.name = inst.name
#           newInst.type = inst.type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm":
#           newInst = MLInstruction("call", ops[0], ops[1], "listGet")
#           newInst.name = inst.name
#           newInst.type = inst.type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi":
#           newInst = MLInstruction("call", ops[0], ops[1], "listAppend")
#           newInst.name = ops[0].name
#           newInst.type = ops[0].type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev": # destructor
#           newInst = MLInstruction("call", ops[0], "listDestruct")
#           b.instructions[i] = newInst


def parseLoops(filename, fnName):
  with open(filename, mode="r") as f:
    foundLines = []
    found = False
    for l in f.readlines():
      if re.match("Printing analysis 'Natural Loop Information' for function '%s':" % fnName, l):
        found = True
      elif found:
        m = re.match("Loop at depth \d+ containing: (\S+)", l.strip())
        if m:
          foundLines.append(m.group(1))
        elif re.match("Printing analysis 'Natural Loop Information' for function '\S+':", l):
          found = False

    LoopInfo = namedtuple("LoopInfo", ["header", "body", "exits", "latches"])

    loops = []
    for m in foundLines:
      header = []
      body = []
      exits = []
      latches = []

      blks = m.replace("%", "").split(",")
      for b in blks:
        name = re.search("([^<]+)", b).group(0)
        print("name: %s" % b)
        if "<header>" in b: header.append(name)
        if "<exiting>" in b: exits.append(name)
        if "<latch>" in b: latches.append(name)
        if "<header>" not in b and "<exiting>" not in b and "latch" not in b: body.append(name)

      loops.append(LoopInfo(header, body, exits, latches))

    for l in loops:
      print("found loop: header: %s, body: %s, exits: %s, latches: %s" % (l.header, l.body, l.exits, l.latches))

    return loops

class CodeInfo:
  def __init__(self, code, modifiedVars, fnArgs):
    self.code = code  # either an inv or ps
    self.modifiedVars = modifiedVars
    self.fnArgs = fnArgs

  def __repr__(self):
    return "code: %s\nmod vars: %s\nfn args: %s" % (self.code, [v.name for v in self.modifiedVars],
                                                   [v.name for v in self.fnArgs])

invNum = 0
def processLoops(header, body, exits, latches, fnArgs):
  havocs = []
  for blk in [header, *body, *exits, *latches]:
    for i in blk.instructions:
      opcode = i.opcode
      ops = list(i.operands)
      if opcode == "store":
        havocs.append(ops[1])

  global invNum
  inv = MLInst.Call("inv%s" % invNum, Type.bool(), *[MLInst.Load(h) for h in havocs], *fnArgs)
  invNum = invNum + 1

  # remove back edges, and replace br with assert inv
  for l in latches:
    l.succs.remove(header)
    header.preds.remove(l)
    l.instructions[-1] = MLInst.Assert(inv)

  # prepend assume inv to header
  header.instructions.insert(0, MLInst.Assume(inv))

  # prepend havocs to header
  if havocs:
    header.instructions.insert(0, MLInst.Havoc(*havocs))

  # append assert inv initialization to header's predecessor
  for p in header.preds:
    p.instructions.insert(-1, MLInst.Assert(inv))

  print("header preds:")
  for p in header.preds:
    for i in p.instructions:
      print("%s" % i)

  print("header:")
  for i in header.instructions:
    print("%s" % i)

  # print("exits:")
  # for e in exits:
  #   for i in e.instructions:
  #     print("%s" % i)

  print("latches:")
  for l in latches:
    print("%s: succ: %s" % (l.name, l.succs))
    for i in l.instructions:
      print("%s" % i)

  return CodeInfo(inv, havocs, fnArgs)

def processBranches(blocksMap, fnArgs):
  retCodeInfo = []
  for b in blocksMap.values():
    opcode = b.instructions[-1].opcode
    ops = list(b.instructions[-1].operands)

    if opcode == "br" and len(ops) > 1:  # a conditional branch
      # XXX: bug in llvmlite that switches the ordering of succs
      b.succs[1].instructions.insert(0, MLInst.Assume(ops[0]))
      b.succs[0].instructions.insert(0, MLInst.Assume(MLInst.Not(ops[0])))

    elif opcode == "switch":
      targets = ops[3::2]
      vals = ops[2::2]
      for t,v in zip(targets, vals):
        blocksMap[t.name].instructions.insert(0, MLInst.Assume(MLInst(ops[0], v)))

      # default fallthrough
      blocksMap[ops[1].name].instructions.insert(0, MLInst.Assume(
                                                    MLInst.Not(MLInst.Or(*[MLInst.Eq(ops[0], v) for v in vals]))))

    elif opcode == "ret":
      filteredArgs = list(filter(lambda a: b"sret" not in a.attributes, fnArgs))  # remove the sret args
      ps = MLInst.Call("ps", Type.bool(), ops[0], *filteredArgs)
      b.instructions.insert(-1, MLInst.Assert(ps))
      retCodeInfo.append(CodeInfo(ps, [ops[0]], filteredArgs))

  return retCodeInfo

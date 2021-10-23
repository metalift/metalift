import re
from collections import defaultdict
from copy import deepcopy

from llvmlite.binding import TypeRef, ValueRef
from llvmlite.ir import Argument

import models
from ir import Expr, Type, parseTypeRef, Var, Call, Lit, Bool, Int, List, Set, Eq, Lt, Le, Not, Or, And, Implies, Synth, Ite, \
  Add, Sub, Mul, BoolLit

from vc_util import parseOperand

class State:
  def __init__(self):
    self.regs = {}
    self.mem = {}
    self.args = []
    self.vc = None
    self.assumes = []

  def __repr__(self):
    # keys are ValueRef objs
    return "regs: %s\nmem: %s\nvc: %s\n" % \
           (", ".join(["%s: %s" % (k.name, v) for (k,v) in self.regs.items()]),
            ", ".join(["%s: %s" % (k.name, v) for (k,v) in self.mem.items()]),
            self.vc)

class Block:
  def __init__(self, name, instructions):
    self.name = name
    self.instructions = instructions
    self.preds = []
    self.succs = []
    self.state = State()

  def __repr__(self):
    return "name: %s, pred: %s, succ: %s" % (self.name, ",".join([p.name for p in self.preds]),
                                             ",".join([s.name for s in self.succs]))

class VC:

  def __init__(self):
    self.vars = set()
    self.havocNum = 0
    self.preds = dict()

  def makeVar(self, name, ty):
    if isinstance(ty, TypeRef): ty = parseTypeRef(ty)
    elif isinstance(ty, Type): pass
    else: raise Exception("NYI %s with type %s" % (name, ty))

    e = Var(name, ty)
    found = any(v.args[0] == name and v.type == ty for v in self.vars)
    if not found: self.vars.add(e)

    return e

  def callPred(self, name, returnT: Type, *args):
    newArgs = [Var("v%s" % i, a.type) for (i, a) in zip(range(len(args)), args)]
    self.preds[name] = Call(name, returnT, *newArgs)
    return Call(name, returnT, *args)

  def computeVC(self, blocksMap, firstBlockName, arguments):
    initBlock = blocksMap[firstBlockName]
    for arg in arguments:
      v = self.makeVar(arg.name, arg.type)
      initBlock.state.regs[arg] = v
      initBlock.state.args.append(v)
      initBlock.state.assumes.append(BoolLit(True))

    # simple loop assuming the blocks are in predecessor order
    #for b in blocksMap.values():
    #  self.compute(b)

    # worklist style loop that doesn't assume any ordering of the blocks
    done = False
    while not done:
      done = True
      for b in blocksMap.values():
        if b.state.vc is None and (not b.preds or all([p.state.vc is not None for p in b.preds])):
          self.compute(b)
          done = False

    blockVCs = [b.state.vc for b in blocksMap.values()]

    body = Implies(And(*blockVCs), self.makeVar(firstBlockName, Bool()))

    invAndPs = [Synth(p.args[0], Lit(True, Bool()), *p.args[1:]) for p in
                filter(lambda p: p.args[0] == "ps" or p.args[0].startswith("inv"), self.preds.values())]
    preds = list(filter(lambda p: not(p.args[0] == "ps" or p.args[0].startswith("inv")), self.preds.values()))

    return self.vars, invAndPs, preds, body


  # merge either the registers or mem dict passed in containers
  def merge(self, containers):
    groups = defaultdict(lambda: defaultdict(list))
    for pname,path,container in containers:
      for k, v in container.items():
        #groups[k][v].append(self.makeVar(pname, bool))
        groups[k][v].append(path)

    merged = dict()
    for k, vals in groups.items():
      if len(vals) == 1:
        merged[k] = list(vals.keys())[0]
      else:
        valPaths = dict()
        for v in vals:
          paths = [And(*pathStack) if len(pathStack) > 1 else pathStack[0] for pathStack in vals[v]]
          valPaths[v] = Or(*paths) if len(paths) > 1 else paths[0]

        e = list(valPaths.items())[0][0]
        for vp in list(valPaths.items())[1:]:
          e = Ite(vp[1], vp[0], e)

        merged[k] = e
        print("merged[%s] = %s" % (k.name, e))

    return merged

  def mergeStates(self, preds):
    if len(preds) == 1:
      s = State()
      src = preds[0].state
      s.regs = dict([(k, deepcopy(v)) for k,v in src.regs.items()])
      s.mem = dict([(k, deepcopy(v)) for k,v in src.mem.items()])
      s.args = deepcopy(src.args)
      s.assumes = deepcopy(src.assumes)
      return s

    else:  # merge
      s = State()
      s.regs = self.merge([p.name, p.state.assumes, p.state.regs] for p in preds)
      s.mem = self.merge([p.name, p.state.assumes, p.state.mem] for p in preds)

      s.args = preds[0].state.args

      # vc should be None

      assumeE = [And(*p.state.assumes) if len(p.state.assumes) > 1 else p.state.assumes[0] for p in preds]
      s.assumes.append( Or(*assumeE) if len(assumeE) > 1 else assumeE[0] )

      return s

  def formVC(self, blockName, regs, assigns, assumes, asserts, succs):
    # concat all assignments
    if not assigns: assignE = None
    elif len(assigns) == 1:  # r1 = v1
      a = list(assigns)[0]
      assignE = Eq(self.makeVar(a.name, a.type), regs[a])
    else:  # r1 = v1 and r2 = v2 ...
      assignE = And(*[Eq(self.makeVar(r.name, r.type), regs[r]) for r in assigns])

    if not assumes: assumeE = None
    elif len(assumes) == 1: assumeE = assumes[0]
    else: assumeE = And(*assumes)

    if not assignE and not assumeE: lhs = None
    elif assignE and not assumeE: lhs = assignE
    elif not assignE and assumeE: lhs = assumeE
    else: lhs = And(assignE, assumeE)

    if not succs: succE = None
    elif len(succs) == 1: succE = self.makeVar(succs[0].name, Bool())
    else: succE = And(*[self.makeVar(s.name, Bool()) for s in succs])

    if not asserts: assertE = None
    elif len(asserts) == 1: assertE = asserts[0]
    else: assertE = And(*asserts)

    if not succE and not assertE: rhs = None
    elif succE and not assertE: rhs = succE
    elif not succE and assertE: rhs = assertE
    else: rhs = And(succE, assertE)

    vc = Eq(self.makeVar(blockName, Bool()), rhs if not lhs else Implies(lhs, rhs))

    return vc

  def compute(self, b: Block):
    s = self.mergeStates(b.preds) if b.preds else b.state
    assigns = set()
    asserts = list()

    print("block: %s" % b.name)
    for i in b.instructions:
      print("inst: %s" % i)

      opcode = i.opcode
      ops = list(i.operands)

      if opcode == "alloca":
        # alloca <type>, align <num> or alloca <type>
        t = re.search("alloca ([^$|,]+)", str(i)).group(1)  # bug: ops[0] always return i32 1 regardless of type
        if t == "i32": s.mem[i] = Lit(0, Int())
        elif t == "i8": s.mem[i] = Lit(False, Bool())
        elif t == "i1": s.mem[i] = Lit(False, Bool())
        elif t == "%struct.list*": s.mem[i] = Lit(0, List(Int()))
        elif t == "%struct.set*": s.mem[i] = Lit(0, Set(Int()))
        else: raise Exception("NYI: %s" % i)

      elif opcode == "load":
        s.regs[i] = s.mem[ops[0]]
        assigns.add(i)

      elif opcode == "store":
        # store either a reg or a literal
        s.mem[ops[1]] = VC.parseOperand(ops[0], s.regs)

      elif opcode in ("add", "sub", "mul"):
        op1 = VC.parseOperand(ops[0], s.regs)
        op2 = VC.parseOperand(ops[1], s.regs)
        if opcode == "add": s.regs[i] = Add(op1, op2)
        elif opcode == "sub": s.regs[i] = Sub(op1, op2)
        elif opcode == "mul": s.regs[i] = Mul(op1, op2)

      elif opcode == "icmp":
        cond = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(i).strip()).group(1)
        op1 = VC.parseOperand(ops[0], s.regs)
        op2 = VC.parseOperand(ops[1], s.regs)

        if cond == "eq": r = Eq(op2, op1)
        elif cond == "sgt": r = Lt(op2, op1)
        elif cond == "sle": r = Le(op1, op2)
        elif cond == "slt" or cond == "ult": r = Lt(op1, op2)
        else: raise Exception("NYI %s" % cond)

        s.regs[i] = r
        assigns.add(i)

      elif opcode == "br" or opcode == "ret" or opcode == "switch":
        pass

      elif opcode == "bitcast" or opcode == "sext":
        s.regs[i] = VC.parseOperand(ops[0], s.regs)


      elif opcode == "call":  # last arg is fn to be called
        fnName = ops[-1] if isinstance(ops[-1], str) else ops[-1].name
        if fnName in models.fnModels:
          r = models.fnModels[fnName](s.regs, *ops[:-1])
          # print("ret: %s, %s" % (r.val, r.assigns))
          if r.val:
            s.regs[i] = r.val
            assigns.add(i)
          if r.assigns:
            for k,v in r.assigns:
              s.regs[k] = v
              assigns.add(k)

        else: raise Exception("NYI: %s, name: %s" % (i, fnName))


      elif opcode == "assert":
        e = VC.evalMLInst(ops[0], s.regs, s.mem)
        # e = ops[0]
        # if e.opcode == "call":
        #   name = e.operands[-1]
        #   if name.startswith("inv"):
        #     parsed = [VC.evalMLInst(arg, s.regs, s.mem) for arg in e.operands[0:-1]]
        #     e = self.callPred(name, Bool(), *parsed)
        #     #parsed = VC.parseExpr(e, s.regs, s.mem)
        #     #e = self.callPred(parsed.args[0], parsed.type, *parsed.args[1:])
        #
        #   elif name == "ps":
        #     parsed = [VC.evalMLInst(arg, s.regs, s.mem) for arg in e.operands[0:-1]]
        #     e = self.callPred(name, Bool(), *parsed)
        #
        #     # parsed = VC.evalMLInst(e, s.regs, s.mem)
        #     # e = self.callPred(parsed.args[0], parsed.type, *parsed.args[1:])
        #   else: raise Exception("NYI: %s" % i)
        # else: raise Exception("NYI: %s" % i)

        asserts.append(e)

      elif opcode == "assume":
        s.assumes.append(VC.evalMLInst(ops[0], s.regs, s.mem))
        # if isinstance(ops[0], MLInstruction):
        #   s.assumes.append(VC.evalMLInst(ops[0], s.regs, s.mem))
        # elif isinstance(ops[0], ValueRef):
        #   s.assumes.append(VC.parseOperand(ops[0], s.regs))
        # else: raise Exception("NYI: %s" % i)

      elif opcode == "havoc":
        for op in ops:
          s.mem[op] = self.makeVar("%s_%s" % (op.name, self.havocNum), s.mem[op].type)
          self.havocNum = self.havocNum + 1

      else:
        raise Exception("NYI: %s" % i)

    s.vc = self.formVC(b.name, s.regs, assigns, s.assumes, asserts, b.succs)

    print("final state: %s" % s)
    b.state = s
    return s

  # evaluate a ML instruction. returns an IR Expr
  @staticmethod
  def evalMLInst(i, reg, mem):
    if isinstance(i, ValueRef): return reg[i]
    elif isinstance(i, str): return i
    elif i.opcode == "load": return mem[i.operands[0]]
    elif i.opcode == "not": return Not(VC.evalMLInst(i.operands[0], reg, mem))
    elif i.opcode == "or": return Or(VC.evalMLInst(i.operands[0], reg, mem))
    elif i.opcode == "call": return Call(i.operands[0], i.operands[1],
                                         *[VC.evalMLInst(a, reg, mem) for a in i.operands[2:]])
    else: raise Exception("NYI: %s" % i)


  @staticmethod
  def parseOperand(op, reg, hasType = True):
    return parseOperand(op, reg, hasType)

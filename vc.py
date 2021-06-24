import re
from collections import defaultdict
from copy import deepcopy

from llvmlite.binding import TypeRef

from ir import Expr

class State:
  def __init__(self):
    self.regs = {}
    self.mem  = {}
    self.args = []
    self.vc = None

  def __repr__(self):
    return "regs: %s\nmem: %s" % (self.regs, self.mem)

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
    self.preds = dict()

  def makeVar(self, name, ty):
    if isinstance(ty, TypeRef):
      if str(ty) == "i32":  # ty.name returns empty string. possibly bug
        ty = "Int"
      elif str(ty) == "i1":
        ty = "Bool"
      else:
        raise Exception("NYI %s" % ty.name)
    else:
      if ty == int:
        ty = "Int"
      elif ty == bool:
        ty = "Bool"
      else:
        raise Exception("NYI %s" % ty)
    e = Expr.Var(name, ty)
    self.vars.add(e)
    return e

  def callPred(self, name, *args):
    retType = args[-1]
    if retType == int:
      retType = "Int"
    elif retType == bool:
      retType = "Bool"
    else:
      raise Exception("NYI %s" % retType)
    p = Expr.Pred(name, *args[0:-1], retType)
    self.preds[name] = p
    return p

  def computeVC(self, blocksMap, firstBlockName, arguments):
    initBlock = blocksMap[firstBlockName]
    for arg in arguments:
      name = arg.name
      v = self.makeVar(name, arg.type)
      initBlock.state.regs[name] = v
      initBlock.state.args.append(v)

    # simple loop assuming the blocks are in predecessor order
    #for b in blocksMap.values():
    #  self.computeBlockVC(b)

    # worklist style loop that doesn't assume any ordering of the blocks
    done = False
    while not done:
      done = True
      for b in blocksMap.values():
        if b.state.vc is None and (not b.preds or all([p.state.vc is not None for p in b.preds])):
          self.computeBlockVC(b)
          done = False

    blockVCs = [b.state.vc for b in blocksMap.values()]
    vc = Expr.Assert(Expr.Not(Expr.Implies(Expr.And(*blockVCs), self.makeVar(firstBlockName, bool))))

    return self.vars, self.preds.values(), vc

  def mergeStates(self, preds):
    if len(preds) == 1:
      return deepcopy(preds[0].state)
    else: # merge
      s = State()

      reg_d = defaultdict(set)
      mem_d = defaultdict(set)
      for p in preds:
        for k, v in p.state.regs.items():
          reg_d[k].add( (self.makeVar(p.name, bool), v) )
        for k, v in p.state.mem.items():
          mem_d[k].add( (self.makeVar(p.name, bool), v) )

      for k, v in reg_d.items():
        if len(v) == 1:
          s.regs[k] = v
        else:
          l = list(v)  # [ (p1, v1), (p2, v2) ]
          sameVal = all( val == l[0][1] for (p, val) in l)
          if sameVal:
            s.regs[k] = l[0][1]
          else:
            e = Expr.Ite(l[0][0], l[0][1], Expr.Lit(0))
            for path, val in l[1:]:
              e = Expr.Ite(path, val, e)
            s.regs[k] = e

      for k, v in mem_d.items():
        if len(v) == 1:
          s.mem[k] = v
        else:
          l = list(v)  # [ (p1, v1), (p2, v2) ]
          sameVal = all( val == l[0][1] for (p, val) in l)
          if sameVal:
            s.mem[k] = l[0][1]
          else:
            e = Expr.Ite(l[0][0], l[0][1], Expr.Lit(0))
            for path, val in l[1:]:
              e = Expr.Ite(path, val, e)
            s.mem[k] = e

      s.args = preds[0].state.args
      return s

  def computeBlockVC(self, b : Block):
    s = self.mergeStates(b.preds) if len(b.preds) > 0 else b.state
    assigns = set()

    print("block: %s" % b.name)
    for i in b.instructions:
      print("inst: %s" % i)

      opcode = i.opcode
      ops = list(i.operands)

      if opcode == "alloca":
        type = str(ops[0])
        if type == "i32 1":
          v = 0
        elif type == "i1":
          v = False
        else:
          raise Exception("NYI: %s" % type)
        s.mem[i.name] = v

      elif opcode == "load":
        s.regs[i.name] = s.mem[ops[0].name]
        assigns.add(i.name)

      elif opcode == "store":
        # store either a reg or a literal
        s.mem[ops[1].name] = VC.parseOperand(ops[0], True)

      elif opcode == "icmp":
        cond = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(i).strip()).group(1)
        op1 = VC.parseOperand(ops[0], True)
        if not VC.isLiteral(op1): op1 = s.regs[op1]
        op2 = VC.parseOperand(ops[1], True)
        if not VC.isLiteral(op2): op2 = s.regs[op2]

        if cond == "sgt":
          r = Expr.Lt(op1, op2)
        else:
          raise Exception("NYI")

        s.regs[i.name] = r
        assigns.add(i.name)

      elif opcode == "br" or opcode == "ret" or opcode == "switch":
        # concat all assignments
        ass = Expr.And(*[Expr.Eq(r, s.regs[r]) for r in assigns]) if len(assigns) else None

        if opcode == "br":
          # successor blocks
          succs = self.makeVar(ops[0].name, bool) if len(ops) == 1 else \
                  Expr.And(*[self.makeVar(op.name, bool) for op in ops])  #, makeVar(ops[2].name, bool))
        else:  # ret -- assert postcondition
          succs = self.callPred("ps", self.makeVar(ops[0].name, ops[0].type), *s.args, bool)

        succ_expr = succs if ass is None else Expr.Implies(ass, succs)
        s.vc = Expr.Iff(self.makeVar(b.name, bool), succ_expr)
        print("vc: %s" % s.vc)

      else:
        raise Exception("NYI: %s" % i)

    print("s: %s" % s)
    b.state = s
    return s

  @staticmethod
  def parseOperand(op, hasType = False):
    if op.name:  # a reg
      return op.name
    elif hasType:  # i32 0
      return int(re.search("(\w+) (\d+)", str(op)).group(2))
    else:  # 0
      return int(op)

  @staticmethod
  def isLiteral(v):
    return isinstance(v, int)

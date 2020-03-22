from collections import defaultdict, deque
from enum import Enum, auto

import ir
from frontend import python
from visitor import Visitor, PassthruVisitor

class CFGBuilder(PassthruVisitor):

  class FlowType(Enum):
    Normal = auto()
    LoopBack = auto()
    LoopExit = auto()

    def __repr__(self):
      return self.name

  def __init__(self):
    super().__init__(self.__class__.__name__)
    self.succs = defaultdict(set)
    self.preds = defaultdict(set)
    self.loops = deque()  # stack of (While, exit stmt) pairs representing the current context of loops

  def update(self, code, pred, succ, pred_type=FlowType.Normal, succ_type=FlowType.Normal):
    if isinstance(pred, list):
      for p in pred:
        self.succs[(p, pred_type)].add(code)
    else:
      self.succs[(pred, pred_type)].add(code)
    self.preds.setdefault((code, pred_type), set()).update(pred if isinstance(pred, list) else [pred])

    if isinstance(succ, list):
      for s in succ:
        self.preds[(s, succ_type)].add(code)
    else:
      self.preds[(succ, succ_type)].add(code)
    self.succs.setdefault((code, succ_type), set()).update(succ if isinstance(succ, list) else [succ])

  def construct_cfg(self, code, pred=None, succ=None):
    if isinstance(code, ir.Block):
      s = succ
      p = pred
      l = len(code.stmts)
      for i in range(l):
        if l > 1 and i == 0:  # first stmt in list of length > 1
          s = code.stmts[1]
        elif l > 1 and i == l - 1:  # last stmt in list of length > 1
          p = code.stmts[-2]
        elif l > 1:  # stmt in the middle of a list of length > 1
          p = code.stmts[i - 1]
          s = code.stmts[i + 1]
        self.construct_cfg(code.stmts[i], p, s)
        s = succ
        p = pred

    elif isinstance(code, ir.If):
      self.update(code, pred, succ)
      self.construct_cfg(code.conseq, code, succ)
      self.construct_cfg(code.alt, code, succ)

    elif isinstance(code, ir.Assign) or isinstance(code, ir.ExprStmt) or isinstance(code, ir.Assert):
      if isinstance(succ, ir.While) and self.loops and self.loops[-1][0] == succ:
        self.update(code, pred, succ, CFGBuilder.FlowType.Normal, CFGBuilder.FlowType.LoopBack)
      else:
        self.update(code, pred, succ)

    elif isinstance(code, ir.While):
      self.loops.append((code, succ))
      self.update(code, pred, [code.body.stmts[0], succ])
      self.construct_cfg(code.body, code, code)
      self.loops.pop()

    elif isinstance(code, ir.Branch):
      (loop, exit) = self.loops[-1]
      if code.type == ir.Branch.Type.Break:
        self.update(code, pred, exit, CFGBuilder.FlowType.Normal, CFGBuilder.FlowType.LoopExit)
      elif code.type == ir.Branch.Type.Continue:
        self.update(code, pred, loop, CFGBuilder.FlowType.Normal, CFGBuilder.FlowType.LoopBack)
      else:
        raise TypeError('Unknown branch type: %s' % code)

    elif isinstance(code, ir.Return):
      self.update(code, pred, None)

    elif isinstance(code, ir.FnDecl):
      self.construct_cfg(code.body, pred, succ)

    else:
      raise TypeError('NYI: %s' % code)


## test code below

# t = python.translate_file('example/unstructured_loop.py')
# c = CFGBuilder()
# c.construct_cfg(t.fns['vctest'], None, None)
#
# for (code, pred) in c.preds.items():
#   print('stmt: %s pred: %s' % (code, pred))
#
# for (code, suc) in c.succs.items():
#   print('stmt: %s succ: %s' % (code, suc))

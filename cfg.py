from collections import defaultdict, deque

import ir
from frontend import python
from visitor import Visitor, PassthruVisitor

class CFGBuilder(PassthruVisitor):
  def __init__(self):
    super().__init__(self.__class__.__name__)
    self.succs = defaultdict(set)
    self.preds = defaultdict(set)
    self.loops = deque()  # stack of (While, exit stmt) pairs representing the current context of loops

  def update(self, code, pred, succ):
    if isinstance(pred, list):
      for p in pred:
        self.succs[p].add(code)
    else:
      self.succs[pred].add(code)
    self.preds.setdefault(code, set()).update(pred if isinstance(pred, list) else [pred])

    if isinstance(succ, list):
      for s in succ:
        self.preds[s].add(code)
    else:
      self.preds[succ].add(code)
    self.succs.setdefault(code, set()).update(succ if isinstance(succ, list) else [succ])

  def construct_cfg(self, code, pred, succ):
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
      self.update(code, pred, succ)

    elif isinstance(code, ir.While):
      self.loops.append((code, succ))
      self.update(code, pred, [code.body.stmts[0], succ])
      self.construct_cfg(code.body, code, code)
      self.loops.pop()

    elif isinstance(code, ir.Branch):
      (loop, exit) = self.loops[-1]
      if code.type == ir.Branch.Type.Break:
        self.update(code, pred, exit)
      elif code.type == ir.Branch.Type.Continue:
        self.update(code, pred, loop)
      else:
        raise TypeError('Unknown branch type: %s' % code)

    elif isinstance(code, ir.Return):
      self.update(code, pred, None)

    elif isinstance(code, ir.FnDecl):
      self.construct_cfg(code.body, pred, succ)

    else:
      raise TypeError('NYI: %s' % code)


## test code below
# t = python.translate_file('example/nested_loops.py')
# c = CFGBuilder()
# c.construct_cfg(t.fns['vctest'], None, None)
#
# for (code, p) in c.preds.items():
#   print('stmt: %spred: %s' % (code, p))
#
# for (code, s) in c.succs.items():
#   print('stmt: %ssucc: %s' % (code, s))

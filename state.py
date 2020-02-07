from collections import deque
from copy import deepcopy
import ir

class Frame:
  def __init__(self):
    self.vars = {}  # maps Vars to Exprs
    self.assumes = deque()
    self.rv = None

  def __repr__(self):
    return 'state: %s \n%s\n%s' % (self.vars, self.assumes, self.rv)

class State:
  def __init__(self):
    self.frames = deque()
    self.frames.append(Frame())

  def __repr__(self):
    return 'frames:\n %s\n' % '\n'.join(str(f) for f in self.frames)

  # Standard stack functions
  def top(self):
    return self.frames[-1]

  def pop(self):
    return self.frames.pop()

  def push(self, vars):
    f = Frame()
    f.vars = vars
    self.frames.append(f)

  # Utility functions for interpreter.py
  def newFrame(self):
    f = Frame()
    self.frames.append(f)

  def dupFrame(self):
    f = Frame()
    f.vars = deepcopy(self.top().vars)
    self.frames.append(f)

  def evaluatesTo(self, expr, val):
    self.top().vars[expr] = val

  def evaluate(self, expr):
    return self.top().vars[expr]

  def contains(self, key):
    return key in self.top().vars

  def retVal(self, val):
    self.top().rv = val

  def update(self, frame):
    self.frames[-1] = frame

  def merge(self, test, cons, altr):
    cons_keys = set(cons.vars.keys())
    altr_keys = set(altr.vars.keys())
    keys = cons_keys.union(altr_keys)
    for key in keys:
      cons_val = cons.vars[key]
      altr_val = altr.vars[key]
      if (cons_val == altr_val):
        self.top().vars[key] = cons_val
      else:
        self.top().vars[key] = ir.If(test, cons_val, altr_val)
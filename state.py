from collections import deque

class Frame:
  def __init__(self):
    self.vars = {}  # maps Vars to Exprs
    self.assumes = deque()
    self.rv = None

  def __repr__(self):
    return 'state: %s \n%s' % (self.vars, self.assumes)

class State:
  def __init__(self):
    self.frames = deque()
    self.frames.append(Frame())

  def __repr__(self):
    return 'frames:\n %s\n' % '\n'.join(f for f in self.frames)

  def pop(self):
    self.frames.pop()

  def push(self, vars):
    f = Frame()
    f.vars = vars
    self.frames.append(f)


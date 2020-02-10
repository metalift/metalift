import subprocess

import ir
import visitor
from rosette import RosetteTranslator

class ChoiceReplacer(visitor.PassthruVisitor):
  def __init__(self, choices):
    super().__init__(self.__class__.__name__)
    self.choices = choices
    self.choice_num = 0

  def visit_Choose(self, n):
    r = n.args[self.choices[self.choice_num]]
    self.choice_num = self.choice_num + 1
    return r

def remove_choices(p, choices):
  return ChoiceReplacer(choices).visit(p)

rosette_tmpfile = '/tmp/ex.rkt'
racket_path = 'racket' # path to racket exe
def synthesize(n: ir.Program, lang: ir.Program, inv_fn, ps_fn):
  new_stmts = []

  # add language definition
  for s in lang.stmts:
    if isinstance(s, ir.FnDecl):
      new_stmts.append(s)

  for s in n.stmts:
    if isinstance(s, ir.FnDecl):
      if s.name.startswith('inv') or s.name == 'ps':
        new_body = inv_fn(s.args) if s.name.startswith('inv') else ps_fn(s.args)
        new_stmts.append(ir.FnDecl(s.name, s.args, s.rtype, new_body))
    else:
      new_stmts.append(s)

  mod_prog = ir.Program(n.imports, new_stmts)

  rt = RosetteTranslator()
  with open(rosette_tmpfile, 'w') as f:
    f.write(rt.to_rosette(mod_prog))

  result = subprocess.check_output([racket_path, rosette_tmpfile],
                                   stderr=subprocess.STDOUT)
  #print('result: %s' % result)

  choices = rt.parse_output(result)
  # print('choices: %s' % choices)

  mod_prog = remove_choices(mod_prog, choices)

  return mod_prog
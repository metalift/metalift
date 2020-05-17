import subprocess

import ir
import visitor
from rosette import RosetteTranslator
from z3translator import Z3Translator


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

extra_fns = []
def declare(*fns: ir.FnDecl):
  global extra_fns
  extra_fns.extend(fns)

rosette_synfile = '/tmp/s.rkt'
rosette_verfile = '/tmp/v.z3'
racket_path = 'racket'  # path to racket exe
z3_path = 'z3'  # path to z3 exe
def synthesize(n: ir.Program, lang: ir.Program, info, inv_fn, ps_fn):
  new_stmts = []

  # add language definition
  for s in lang.stmts:
    if isinstance(s, ir.FnDecl):
      new_stmts.append(s)

  # add search function output
  for s in n.stmts:
    if isinstance(s, ir.FnDecl):

      if s.name.startswith('inv') or s.name.endswith('_ps'):
        ast_info = info[s]
        read_vars = {a.name: a for a in ast_info[0]}
        write_vars = {a.name: a for a in ast_info[1]}
        new_body = inv_fn(ast_info[0], read_vars, write_vars) if s.name.startswith('inv') else \
                   ps_fn(ast_info[0], read_vars, write_vars)
        new_stmts.append(ir.FnDecl(s.name, s.args, s.rtype, new_body))
    else:
      new_stmts.append(s)

  # add user defined functions
  new_stmts.extend(extra_fns)

  mod_prog = ir.Program(n.imports, new_stmts)

  print("mod prog: %s" % mod_prog)

  # synthesis
  rt = RosetteTranslator(True, max_num=4)
  with open(rosette_synfile, 'w') as f:
    f.write(rt.to_rosette(mod_prog))

  result = subprocess.check_output([racket_path, rosette_synfile], stderr=subprocess.STDOUT)
  print('synthesis result: %s' % result)

  choices = rt.parse_output(result)
  print('choices: %s' % choices)

  mod_prog = remove_choices(mod_prog, choices)

  # verification
  # rt = RosetteTranslator(False)
  # with open(rosette_verfile, 'w') as f:
  #   f.write(rt.to_rosette(mod_prog))
  #
  # result = subprocess.check_output([racket_path, rosette_verfile], stderr=subprocess.STDOUT)
  # print('verification result: %s' % str(result))

  z3 = Z3Translator()
  with open(rosette_verfile, 'w') as f:
    f.write(z3.to_z3(mod_prog))

  result = subprocess.check_output([z3_path, rosette_verfile], stderr=subprocess.STDOUT)
  print('verification result: %s' % str(result))

  return mod_prog

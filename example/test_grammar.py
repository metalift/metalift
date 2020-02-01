from typing import List
from ir import Var, Choose
from interpreter import SearchGrammar

test123 = 123

@SearchGrammar
def search_space_1a(vars: List[Var]) -> int:
  return 1

@SearchGrammar
def search_space_1b(vars: List[Var]) -> int:
  return 1 + True + 2

@SearchGrammar
def search_space_1c(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  return 1 + Choose(*int_vars)

@SearchGrammar
def search_space_1d(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  return 1 + 1 + Choose(*int_vars) + 1

args = list([Var("x", int), Var("y", int), Var("z", float)])
print(search_space_1a(args))
print(search_space_1b(args))
print(search_space_1c(args))
print(search_space_1d(args))

#def search_space_2a(vars: List[Var], depth: int) -> Stmt:
#  if depth == 0:
#    return 1 + 1 + Choose(*vars) + 1
#  else:
#    return Choose(*vars) + Choose(1, 2, 3, 4)
#
# def search_space_2b(vars: List[Var]) -> Stmt:
#   if Choose(*vars) > 0:
#     return 1
#   else:
#     return 2
#
# def search_space_3a(vars: List[Var], depth: int) -> Stmt:
#   return Choose(*vars) + search_space_3a(vars, depth - 1)
#
# def search_space_3b(vars: List[Var], depth: int) -> Stmt:
#   return 1 + search_space_3b(vars, depth - 1)
#
# def search_space_3c(vars: List[Var], depth: int) -> Stmt:
#   return Choose(*vars) + 1 + search_space_3c(vars, depth - 1)
#
# def search_space_3d(vars: List[Var], depth: int) -> Stmt:
#   return 1 + Choose(*vars) + search_space_3d(vars, depth - 1)
#
# def search_space_4(vars: List[Var], depth: int) -> Stmt:
#   if depth == 0:
#     return Choose(*vars) + Choose(*vars)
#   else:
#     if Choose(True, False):
#       return search_space_4(vars, 0)
#     else:
#       return search_space_4(vars, depth - 1) + search_space_4(vars, depth - 1)

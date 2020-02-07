from typing import List
from ir import Var, Choose
from interpreter import SearchGrammar

### Constant generators

@SearchGrammar
def search_space_1a() -> int:
  return 1

@SearchGrammar
def search_space_1b() -> int:
  return 1 + True + 2

### Generators with symbolic variables

@SearchGrammar
def search_space_1c(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  return 1 + Choose(*int_vars)

@SearchGrammar
def search_space_1d(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  return 1 + 1 + Choose(*int_vars) + 1

### Generators with conditionals (that can be evaluated AOT)

@SearchGrammar
def search_space_2a(vars: List[Var], depth: int) -> int:
  int_vars = [var for var in vars if var.type == int]
  if depth == 0:
    return 3 + Choose(*int_vars)
  else:
    return Choose(*int_vars) + Choose(1, 2, 3, 4)

@SearchGrammar
def search_space_2b(vars: List[Var], depth: int) -> int:
  int_vars = [var for var in vars if var.type == int]
  if depth == 0:
    ret = 3 + Choose(*int_vars)
  else:
    ret = Choose(*int_vars) + Choose(1, 2, 3, 4)
  return ret

### Generators with symbolic conditionals

@SearchGrammar
def search_space_2c(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  if Choose(*int_vars) > 0:
    return 1
  else:
    return 2

@SearchGrammar
def search_space_2d(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  if Choose(*int_vars) > 0:
    ret = 1
  else:
    ret = 2
  return ret

@SearchGrammar
def search_space_2e(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  ret = 2
  if Choose(*int_vars) > 0:
    ret = 1
  return ret

@SearchGrammar
def search_space_2f(vars: List[Var]) -> int:
  int_vars = [var for var in vars if var.type == int]
  if Choose(*int_vars) > 0:
    return 1
  return 2

args = list([Var("x", int), Var("y", int), Var("z", float)])

print("------ Running search_space_1a() -------")
print(search_space_1a(), "\n")

print("------ Running search_space_1b() -------")
print(search_space_1b(), "\n")

print("----- Running search_space_1c(args) ----")
print(search_space_1c(args), "\n")

print("----- Running search_space_1d(args) ----")
print(search_space_1d(args), "\n")

print("--- Running search_space_2a(args, 0) ---")
print(search_space_2a(args, 0), "\n")

print("--- Running search_space_2a(args, 1) ---")
print(search_space_2a(args, 1), "\n")

print("--- Running search_space_2b(args, 0) ---")
print(search_space_2b(args, 0), "\n")

print("--- Running search_space_2b(args, 1) ---")
print(search_space_2b(args, 1), "\n")

print("----- Running search_space_2c(args) ----")
print(search_space_2c(args), "\n")

print("----- Running search_space_2d(args) ----")
print(search_space_2d(args), "\n")

print("----- Running search_space_2e(args) ----")
print(search_space_2e(args), "\n")

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

from abc import abstractmethod
from typing import Generic, Set, TypeVar

from metalift.ir import Add, And, Assert, Axiom, Call, CallValue, Choose, Constraint, Eq, Expr, FnDecl, FnDeclRecursive, FnDefine, Ge, Gt, Implies, Ite, Lambda, Le, Let, Lit, Lt, Mul, NonTerm, Not, Object, Or, Sub, Synth, Target, TargetCall, Tuple, TupleGet, Var


T = TypeVar("T")

class Visitor(Generic[T]):

  @abstractmethod
  def visit_Var(self, o: Var) -> T:
    pass
  
  @abstractmethod
  def visit_NonTerm(self, o: NonTerm) -> T:
    pass

  @abstractmethod
  def visit_Lit(self, o: Lit) -> T:
    pass

  @abstractmethod
  def visit_Object(self, o: Object) -> T:
    pass

  @abstractmethod
  def visit_Add(self, o: Add) -> T:
    pass

  @abstractmethod
  def visit_Sub(self, o: Sub) -> T:
    pass

  @abstractmethod
  def visit_Mul(self, o: Mul) -> T:
    pass

  @abstractmethod
  def visit_Eq(self, o: Eq) -> T:
    pass

  @abstractmethod
  def visit_Lt(self, o: Lt) -> T:
    pass

  @abstractmethod
  def visit_Le(self, o: Le) -> T:
    pass

  @abstractmethod
  def visit_Gt(self, o: Gt) -> T:
    pass

  @abstractmethod
  def visit_Ge(self, o: Ge) -> T:
    pass

  @abstractmethod
  def visit_And(self, o: And) -> T:
    pass

  @abstractmethod
  def visit_Or(self, o: Or) -> T:
    pass

  @abstractmethod
  def visit_Not(self, o: Not) -> T:
    pass

  @abstractmethod
  def visit_Implies(self, o: Implies) -> T:
    pass

  @abstractmethod
  def visit_Ite(self, o: Ite) -> T:
    pass

  @abstractmethod
  def visit_Let(self, o: Let) -> T:
    pass

  @abstractmethod
  def visit_Call(self, o: Call) -> T:
    pass

  @abstractmethod
  def visit_CallValue(self, o: CallValue) -> T:
    pass

  @abstractmethod
  def visit_Assert(self, o: Assert) -> T:
    pass

  @abstractmethod
  def visit_Constraint(self, o: Constraint) -> T:
    pass

  @abstractmethod
  def visit_Tuple(self, o: Tuple) -> T:
    pass

  @abstractmethod
  def visit_TupleGet(self, o: TupleGet) -> T:
    pass

  @abstractmethod
  def visit_Axiom(self, o: Axiom) -> T:
    pass

  @abstractmethod
  def visit_Synth(self, o: Synth) -> T:
    pass

  @abstractmethod
  def visit_Choose(self, o: Choose) -> T:
    pass

  @abstractmethod
  def visit_FnDeclRecursive(self, o: FnDeclRecursive) -> T:
    pass

  @abstractmethod
  def visit_FnDefine(self, o: FnDefine) -> T:
    pass

  @abstractmethod
  def visit_Lambda(self, o: Lambda) -> T:
    pass

  @abstractmethod
  def visit_FnDecl(self, o: FnDecl) -> T:
    pass

  @abstractmethod
  def visit_TargetCall(self, o: TargetCall) -> T:
    pass

  @abstractmethod
  def visit_Target(self, o: Target) -> T:
    pass



class ExtendedVisitor(Visitor[None]):

  def visit_Var(self, o: Var) -> None:
    pass
  
  def visit_NonTerm(self, o: NonTerm) -> None:
    pass

  def visit_Lit(self, o: Lit) -> None:
    pass

  def visit_Object(self, o: Object) -> None:
    pass

  def generic_visit(self, o: Expr, args=None) -> None:
    args = args if args else o.args
    for arg in args:
      arg.accept(self)

  def visit_Add(self, o: Add) -> None:
    self.generic_visit(o)

  def visit_Sub(self, o: Sub) -> None:
    self.generic_visit(o)

  def visit_Mul(self, o: Mul) -> None:
    self.generic_visit(o)

  def visit_Eq(self, o: Eq) -> None:
    self.generic_visit(o)

  def visit_Lt(self, o: Lt) -> None:
    self.generic_visit(o)

  def visit_Le(self, o: Le) -> None:
    self.generic_visit(o)

  def visit_Gt(self, o: Gt) -> None:
    self.generic_visit(o)

  def visit_Ge(self, o: Ge) -> None:
    self.generic_visit(o)

  def visit_And(self, o: And) -> None:
    self.generic_visit(o)

  def visit_Or(self, o: Or) -> None:
    self.generic_visit(o)

  def visit_Not(self, o: Not) -> None:
    self.generic_visit(o)

  def visit_Implies(self, o: Implies) -> None:
    self.generic_visit(o)

  def visit_Ite(self, o: Ite) -> None:
    self.generic_visit(o)

  def visit_Let(self, o: Let) -> None:
    self.generic_visit(o)

  def visit_Call(self, o: Call) -> None:
    self.generic_visit(o, args=o.args[1:])

  def visit_CallValue(self, o: CallValue) -> None:
    self.generic_visit(o)

  def visit_Assert(self, o: Assert) -> None:
    self.generic_visit(o)

  def visit_Constraint(self, o: Constraint) -> None:
    self.generic_visit(o)

  def visit_Tuple(self, o: Tuple) -> None:
    self.generic_visit(o)

  def visit_TupleGet(self, o: TupleGet) -> None:
    self.generic_visit(o)

  def visit_Axiom(self, o: Axiom) -> None:
    self.generic_visit(o)

  def visit_Synth(self, o: Synth) -> None:
    self.generic_visit(o, args=o.args[1:])

  def visit_Choose(self, o: Choose) -> None:
    self.generic_visit(o)

  def visit_FnDeclRecursive(self, o: FnDeclRecursive) -> None:
    self.generic_visit(o, args=o.args[1:])

  def visit_FnDefine(self, o: FnDefine) -> None:
    self.generic_visit(o, args=o.args[1:])

  def visit_Lambda(self, o: Lambda) -> None:
    self.generic_visit(o)

  def visit_FnDecl(self, o: FnDecl) -> None:
    self.generic_visit(o, args=o.args[1:])

  def visit_TargetCall(self, o: TargetCall) -> None:
    self.generic_visit(o)

  def visit_Target(self, o: Target) -> None:
    self.generic_visit(o)


class CountVarsVisitor(ExtendedVisitor):
    vars: Set[Var]

    def __init__(self) -> None:
        self.vars = set()
    
    def visit_Var(self, o: Var) -> None:
        self.vars.add(o)

    def visit_NonTerm(self, o: NonTerm) -> None:
        self.vars.add(o)
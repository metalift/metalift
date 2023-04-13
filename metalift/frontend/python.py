from collections import deque
from typing import Dict, List, Optional, Set, Tuple
from metalift.analysis import CodeInfo
from metalift.analysis_new import VariableTracker

from metalift.ir import And, Assert, Bool, Call, Eq, Expr, Ge, Gt, Implies, Int, IntLit, Ite, Le, Lt, Or, Not, Synth, Type as MLType, Var
from mypy import build
from mypy.build import BuildResult
from mypy.options import Options
from mypy.defaults import PYTHON3_VERSION
from mypy.modulefinder import BuildSource
from mypy.traverser import TraverserVisitor, ExtendedTraverserVisitor
from mypy.nodes import AssignmentStmt, ComparisonExpr, FuncDef, IfStmt, IntExpr, MypyFile, NameExpr, Node as MypyNode, OpExpr, ReturnStmt
from mypy.types import CallableType, Instance, Type as MypyType, UnboundType
from mypy.visitor import ExpressionVisitor

import sys, copy

def parse(path: str, modulename: str) -> Optional[BuildResult]:
    options = Options()
    options.incremental = False  # turn off caching of previously typed results
    # options.export_types = True
    options.show_traceback = True
    options.python_version = PYTHON3_VERSION
    options.preserve_asts = True
    options.export_types = True
    return build.build(sources=[BuildSource(path, modulename, None)], options=options) 

MypyVar = Tuple[str, MypyType]
# Scope = Dict[MypyVar, Var]
# Scope = Dict[str, Var]

class State:
    fn : CallableType
    precond : List[Expr]
    vars: Dict[str, Var]
    asserts : List[Assert]
    has_returned : Bool

    def __init__(
        self,
        fn_type: CallableType = None,
        precond: Optional[List[Expr]] = None, 
        vars: Optional[Dict[str, Var]] = None,
        asserts: List[Assert] = None,
        has_returned: Bool = None
    ) -> None:
        self.fn = fn_type
        self.precond = list() if not precond else precond
        self.vars = dict() if not vars else vars
        self.asserts = list() if not asserts else asserts
        self.has_returned = has_returned if not has_returned else has_returned

    # def read(self, var: str) -> Expr:
    #     for scope in reversed(self.scopes):
    #         # print("scope: %s" % scope)
    #         if var in scope:
    #             return scope[var]
    #     raise RuntimeError(f"{var} not found in scope")

    # def write(self, var: str, val: Expr) -> None:
    #     self.scopes[-1][var] = val
    #     print(f"[{var}] -> {val}")


    def read(self, var: str) -> Expr:
        if var in self.vars:
            return self.vars[var]
        raise RuntimeError(f"{var} not found in {self.vars}")


    def write(self, var: str, val: Expr) -> None:
        self.vars[var] = val
        print(f"[{var}] -> {val}")


    def copy(self) -> "State":
        return State(self.fn,  # mypy.types.CallableType fails to deepcopy
                     copy.deepcopy(self.precond), 
                     copy.deepcopy(self.vars), 
                     copy.deepcopy(self.asserts), 
                     self.has_returned)


def to_mltype(t: MypyType) -> MLType:
    # user annotated types
    if isinstance(t, UnboundType) and t.name == "int":
        return Int()
    
    # inferred types
    elif isinstance(t, Instance) and t.type.fullname == "builtins.int":
        return Int()

    else:
        raise RuntimeError(f"unknown Mypy type: {t}")


class VCVisitor(TraverserVisitor, ExpressionVisitor[Expr]):
# class VCVisitor(ExtendedTraverserVisitor):
    types : Dict[MypyNode, MypyType]
    state : State
    tracker : VariableTracker


    def __init__(self, types, state = None, tracker = None):
        self.types = types
        self.state = State() if not state else state
        self.tracker = VariableTracker() if not tracker else tracker


    def lookup_type_or_none(self, node: MypyNode):
        if node in self.types:
            return self.types[node]
        return None


    def visit_func_def(self, o: FuncDef) -> None:
        print(f"fn {o.name} has type: {o.type}")
        self.state.fn = o.type
        for (n, t) in zip(o.type.arg_names, o.type.arg_types):
            if n is None:
                raise RuntimeError(f"non kw argument not handled: {o.type}")        
            # print(f"arg: {a.variable.name}, type: {a.type_annotation}, " +
            #       f"in ts: {self.lookup_type_or_none(a.variable)}")
            self.state.write(n, self.tracker.variable(n, to_mltype(t)))
    
        if o.type.ret_type is None:
            raise RuntimeError(f"fn must return a value: {o.type}")
        
        self.state.write("rv", self.tracker.variable("rv", to_mltype(o.type.ret_type)))
        
        o.body.accept(self)



    ##
    ## Statements
    ##
    def visit_assignment_stmt(self, o: AssignmentStmt) -> None:
        if len(o.lvalues) > 1:
            raise RuntimeError(f"multi assignments not supported: {o}")
        target = o.lvalues[0].name
        val = o.rvalue.accept(self)
        self.state.write(target, val)


    def visit_if_stmt(self, o: IfStmt) -> None:
        assert len(o.expr) == 1  # not sure why it is a list
        cond = o.expr[0].accept(self)
        print(f"if stmt with cond {cond}")

        # clone the current state
        c_state = self.state.copy()
        c_state.precond.append(cond)
        consequent = VCVisitor(self.types, c_state, self.tracker)
        a_state = self.state.copy()
        a_state.precond.append(Not(cond))
        alternate = VCVisitor(self.types, a_state, self.tracker)

        for s in o.body:
            s.accept(consequent)
        if o.else_body:  # mypy.nodes.Block
            o.else_body.accept(alternate)

        # merge
        c_state = consequent.state
        a_state = alternate.state

        for e in c_state.asserts + a_state.asserts:
            if e not in self.state.asserts:
                self.state.asserts.append(e)

        if c_state.has_returned and a_state.has_returned:
            return
        elif c_state.has_returned and not a_state.has_returned:
            self.state.vars = a_state.vars
        elif not c_state.has_returned and a_state.has_returned:
            self.state.vars = c_state.vars
        else: # both have not returned, need to merge
            for v in set().union(c_state.vars, a_state.vars):
                if v not in self.state.vars and \
                    ((v not in c_state.vars and v in a_state.vars) or \
                    (v in c_state.vars and v not in a_state.vars)):
                    raise RuntimeError(f"{v} only in one of the branches for ite {o}")

            # at this point we know that all vars exist in both c_state and a_state
            for v,c_e in c_state.vars.items():
                a_e = a_state.vars[v]
                if c_e != a_e:
                    self.state.vars[v] = Ite(cond, c_e, a_e)
                else:
                    self.state.vars[v] = c_e

            print(f"merged state: {self.state.vars}")


    def visit_return_stmt(self, o: ReturnStmt) -> None:
        # construct ps: concat all args to this fn, followed by the return value
        ps_args = [Var(n,t) for (n,t) in zip(self.state.fn.arg_names, self.state.fn.arg_types)]
        ps_args.append(o.expr.accept(self))   
        ps = Call("ps", Bool(), *ps_args)

        # generate assertion: path cond -> ps(...)
        if self.state.precond:
            p = And(*self.state.precond) if len(self.state.precond) > 1 else self.state.precond[0]
            ps = Implies(p, ps)

        self.state.asserts.append(ps)
        self.state.has_returned = True
        print(f"add assert: {ps}")
        


    ##
    ## Expressions
    ##
    def visit_int_expr(self, o: IntExpr) -> Expr:
        return IntLit(o.value)


    def visit_name_expr(self, o: NameExpr) -> Expr:
        # return (o.name, self.lookup_type_or_none(o))
        return self.state.read(o.name)


    # a < b < c is equiv to a < b and b < c
    def visit_comparison_expr(self, o: ComparisonExpr) -> Expr:
        operands = [e.accept(self) for e in o.operands]
        e = self.process_comparison(o.operators[0], operands[0], operands[1])
        for i in range(1, len(o.operators)):
            e = e and self.process_comparison(o.operators[i], operands[i], operands[i+1])
        return e


    # ">" | "<" | "==" | ">=" | "<=" | "!=" | "is" ["not"] | ["not"] "in"
    def process_comparison(self, op: str, left: Expr, right: Expr) -> Expr:
        if op == ">":
            return Gt(left, right)
        elif op == "<":
            return Lt(left, right)
        elif op == "==":
            return Eq(left, right)
        elif op == ">=":
            return Ge(left, right)
        elif op == "<=":
            return Le(left, right)
        else:
            raise RuntimeError(f"NYI: {op}")


    # binary expr
    def visit_op_expr(self, o: OpExpr) -> Expr:        
        l = o.left.accept(self)
        r = o.right.accept(self)
        op = o.op
        if op == "+":
            return l + r
        elif op == "-":
            return l - r
        elif op == "*":
            return l * r
        elif op == "/":
            return l / r
        elif op == "%":
            return l % r
        elif op == "and":
            return And(l, r)
        elif op == "or":
            return Or(l, r)
        else:
            raise RuntimeError(f"unknown binary op: {op} in {o}")


    # def visit(self, o: MypyNode) -> bool:
    #     print("contains2: %s" % self.lookup_type_or_none(o))
    #     # If returns True, will continue to nested nodes.
    #     return True

def analyze(
    path: str,
    modulename: str,
    fnNameSuffix: str = "",
    log: bool = True,
) -> Tuple[Set[Var], List[Synth], List[Expr], Expr, List[CodeInfo]]:

    r = parse(path, modulename)
    print("r: %s" % r.graph[modulename].tree)
    # print(f"size of typed dic: {len(r.types)}")

    tree = r.graph[modulename].tree
    assert tree is not None

    v = VCVisitor(r.types)
    tree.accept(v)
    print(f"final asserts: {v.state.asserts}")
    
    return None


if __name__ == "__main__":
    if len(sys.argv) == 1:
        raise RuntimeError("Usage: python.py <input filename>")
    filename = sys.argv[1]
    analyze(filename, "test")

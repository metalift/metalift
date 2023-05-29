import re
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, TypeVar, Union, cast
from metalift.analysis_new import VariableTracker
from metalift.synthesize_rosette import synthesize as run_synthesis

from metalift.ir import (
    And,
    Assert,
    Bool,
    Call,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Ge,
    Gt,
    Implies,
    Int,
    IntLit,
    Ite,
    Le,
    Lt,
    Or,
    Not,
    Synth,
    Type as MLType,
    Var,
)
from mypy import build
from mypy.build import BuildResult
from mypy.options import Options
from mypy.defaults import PYTHON3_VERSION
from mypy.modulefinder import BuildSource
from mypy.traverser import TraverserVisitor
from mypy.nodes import (
    AssertStmt,
    AssignmentStmt,
    Block,
    BreakStmt,
    ClassDef,
    ComparisonExpr,
    ContinueStmt,
    Decorator,
    DelStmt,
    ExpressionStmt,
    ForStmt,
    FuncDef,
    GlobalDecl,
    IfStmt,
    Import,
    ImportAll,
    ImportFrom,
    IntExpr,
    MatchStmt,
    MypyFile,
    NameExpr,
    Expression as MypyExpr,
    NonlocalDecl,
    OpExpr,
    OperatorAssignmentStmt,
    OverloadedFuncDef,
    PassStmt,
    RaiseStmt,
    ReturnStmt,
    Statement,
    TryStmt,
    WhileStmt,
    WithStmt,
)
from mypy.types import CallableType, Instance, ProperType, Type as MypyType, UnboundType
from mypy.visitor import ExpressionVisitor, NodeVisitor, StatementVisitor

import copy

# Run the interpreted version of mypy instead of the compiled one to avoid
# TypeError: interpreted classes cannot inherit from compiled traits
# from https://github.com/python/mypy
# python3 -m pip install --no-binary mypy -U mypy


def parse(path: str, modulename: str) -> BuildResult:
    options = Options()
    options.incremental = False  # turn off caching of previously typed results
    # options.export_types = True
    options.show_traceback = True
    options.python_version = PYTHON3_VERSION
    options.preserve_asts = True
    options.export_types = True
    return build.build(sources=[BuildSource(path, modulename, None)], options=options)


MypyVar = Tuple[str, MypyType]


class State:
    precond: List[Expr]
    vars: Dict[str, Expr]
    asserts: List[Expr]
    has_returned: bool

    def __init__(
        self,
        precond: List[Expr] = list(),
        vars: Dict[str, Expr] = dict(),
        asserts: List[Expr] = list(),
        has_returned: bool = False,
    ) -> None:
        self.precond = precond
        self.vars = vars
        self.asserts = asserts
        self.has_returned = has_returned if not has_returned else has_returned

    def read(self, var: str) -> Expr:
        if var in self.vars:
            return self.vars[var]
        raise RuntimeError(f"{var} not found in {self.vars}")

    def write(self, var: str, val: Expr) -> None:
        self.vars[var] = val
        # print(f"[{var}] -> {val}")

    # def copy(self) -> "State":
    #     return State(self.fn,  # mypy.types.CallableType fails to deepcopy
    #                  copy.deepcopy(self.precond),
    #                  copy.deepcopy(self.vars),
    #                  copy.deepcopy(self.asserts),
    #                  self.has_returned)


def to_mltype(t: MypyType) -> MLType:
    # user annotated types
    if isinstance(t, UnboundType) and t.name == "int":
        return Int()

    # inferred types
    elif isinstance(t, Instance) and t.type.fullname == "builtins.int":
        return Int()

    else:
        raise RuntimeError(f"unknown Mypy type: {t}")


class RWVarsVisitor(TraverserVisitor):
    writes: Set[MypyVar]
    reads: Set[MypyVar]
    types: Dict[MypyExpr, MypyType]

    def __init__(self, types: Dict[MypyExpr, MypyType]) -> None:
        self.writes = set()
        self.reads = set()
        self.types = types

    def visit_assignment_stmt(self, o: AssignmentStmt) -> None:
        if len(o.lvalues) > 1:
            raise RuntimeError(f"multi assignments not supported: {o}")
        lval = cast(
            NameExpr, o.lvalues[0]
        )  # XXX lvalues is a list of Lvalue which can also be indexes or tuples
        t = self.types.get(lval)
        assert t is not None
        self.writes.add((lval.name, t))

        o.rvalue.accept(self)

    # getting here means we are visiting the RHS of an assignment or a general read only expr
    def visit_name_expr(self, o: NameExpr) -> None:
        t = self.types.get(o)
        assert t is not None
        self.reads.add((o.name, t))


class Predicate:
    args: List[MypyVar]
    writes: List[MypyVar]
    reads: List[MypyVar]
    in_scope: List[MypyVar]
    name: str
    grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    ast: Union[WhileStmt, FuncDef]
    synth: Optional[Synth]

    # argument ordering convention:
    # original arguments of the fn first in its original order, then vars that are in scope
    # and not one of the original arguments in sorted order
    def __init__(
        self,
        ast: Union[WhileStmt, FuncDef],
        args: List[MypyVar],
        writes: List[MypyVar],
        reads: List[MypyVar],
        in_scope: List[MypyVar],
        name: str,
        grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> None:
        self.args = args
        self.writes = writes
        self.reads = reads
        self.in_scope = in_scope
        self.name = name
        self.grammar = grammar
        self.ast = ast
        self.synth = None

    def call(self, state: State) -> Call:
        return Call(self.name, Bool(), *[state.read(v[0]) for v in self.args])

    def gen_Synth(self) -> Synth:
        # print(f"gen args: {self.args}, writes: {self.writes}, reads: {self.reads}, scope: {self.in_scope}")

        writes = [Var(v[0], to_mltype(v[1])) for v in self.writes]
        reads = [Var(v[0], to_mltype(v[1])) for v in self.reads]
        in_scope = [Var(v[0], to_mltype(v[1])) for v in self.in_scope]

        v_exprs = [self.grammar(v, self.ast, writes, reads, in_scope) for v in writes]

        body = And(*v_exprs) if len(v_exprs) > 1 else v_exprs[0]

        vars = [Var(v[0], to_mltype(v[1])) for v in self.args]
        return Synth(self.name, body, *vars)


class PredicateTracker:
    types: Dict[MypyExpr, MypyType]
    predicates: Dict[Union[WhileStmt, FuncDef], Predicate]
    num: int  #  current invariant number

    def __init__(self) -> None:
        self.types = dict()
        self.predicates = dict()
        self.num = 0

    def invariant(
        self,
        fn_name: str,
        o: WhileStmt,
        args: List[MypyVar],
        writes: List[MypyVar],
        reads: List[MypyVar],
        in_scope: List[MypyVar],
        grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> Predicate:
        if o in self.predicates:
            return self.predicates[o]
        else:
            non_args_scope_vars = list(set(in_scope) - set(args))
            non_args_scope_vars.sort()
            args = (
                args + non_args_scope_vars
            )  # add the vars that are in scope but not part of args, in sorted order

            inv = Predicate(
                o, args, writes, reads, in_scope, f"{fn_name}_inv{self.num}", grammar
            )
            self.num += 1
            self.predicates[o] = inv
            return inv

    def postcondition(
        self,
        o: FuncDef,
        outs: List[MypyVar],
        ins: List[MypyVar],
        grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> Predicate:
        if o in self.predicates:
            return self.predicates[o]
        else:
            ps = Predicate(o, ins + outs, outs, ins, [], f"{o.name}_ps", grammar)
            self.predicates[o] = ps
            return ps

    def call(self, o: WhileStmt, s: State) -> Call:
        return self.predicates[o].call(s)


class VCVisitor(StatementVisitor[None], ExpressionVisitor[Expr]):
    # class VCVisitor(ExtendedTraverserVisitor):

    fn_name: str
    fn_type: CallableType
    ast: FuncDef
    args: List[Expr]
    ret_val: Optional[Expr]  # remove

    state: State
    invariants: Dict[WhileStmt, Predicate]

    var_tracker: VariableTracker
    pred_tracker: PredicateTracker

    inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]

    types: Dict[MypyExpr, MypyType]

    def __init__(
        self,
        fn_name: str,
        fn_type: CallableType,
        ast: FuncDef,
        args: List[Expr],
        ret_val: Optional[Expr],
        state: State,
        invariants: Dict[WhileStmt, Predicate],
        var_tracker: VariableTracker,
        pred_tracker: PredicateTracker,
        inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        types: Dict[MypyExpr, MypyType],
    ) -> None:
        self.fn_name = fn_name
        self.fn_type = fn_type
        self.ast = ast
        self.args = args
        self.ret_val = ret_val

        self.state = state
        self.invariants = invariants
        self.var_tracker = var_tracker
        self.pred_tracker = pred_tracker

        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar
        self.types = types

    # Definitions

    def visit_assignment_stmt(self, o: AssignmentStmt) -> None:
        if len(o.lvalues) > 1:
            raise RuntimeError(f"multi assignments not supported: {o}")
        target = cast(NameExpr, o.lvalues[0]).name
        self.state.write(target, o.rvalue.accept(self))

    def visit_for_stmt(self, o: ForStmt) -> None:
        raise NotImplementedError()

    def visit_with_stmt(self, o: WithStmt) -> None:
        raise NotImplementedError()

    def visit_del_stmt(self, o: DelStmt) -> None:
        raise NotImplementedError()

    def visit_func_def(self, o: FuncDef) -> None:
        if o.name == self.fn_name:
            fn_type = cast(CallableType, o.type)
            # print(f"analyze fn {o.name} type: {o.type}")
            self.fn_type = fn_type
            self.ret_val = self.var_tracker.variable(
                self.fn_name, to_mltype(fn_type.ret_type)
            )
            self.ast = o

            arg_names = cast(List[str], fn_type.arg_names)
            formals = list(zip(arg_names, fn_type.arg_types))
            self.pred_tracker.postcondition(
                o,
                [(f"{self.fn_name}_rv", self.fn_type.ret_type)],
                formals,
                self.ps_grammar,
            )

            if len(fn_type.arg_names) != len(self.args):
                raise RuntimeError(
                    f"expect {len(fn_type.arg_names)} args passed to {self.fn_name} got {len(self.args)} instead"
                )

            for actual, formal in zip(self.args, formals):
                if to_mltype(formal[1]) != actual.type:
                    raise RuntimeError(
                        f"expect {actual} to have type {to_mltype(formal[1])} rather than {actual.type}"
                    )
                self.state.write(formal[0], actual)

            if fn_type.ret_type is None:
                raise RuntimeError(f"fn must return a value: {fn_type}")

            self.pred_tracker.postcondition(
                o, [(self.fn_name, fn_type.ret_type)], formals, self.ps_grammar
            )

            o.body.accept(self)

    def visit_overloaded_func_def(self, o: OverloadedFuncDef) -> None:
        raise NotImplementedError()

    def visit_class_def(self, o: ClassDef) -> None:
        raise NotImplementedError()

    def visit_global_decl(self, o: GlobalDecl) -> None:
        raise NotImplementedError()

    def visit_nonlocal_decl(self, o: NonlocalDecl) -> None:
        raise NotImplementedError()

    def visit_decorator(self, o: Decorator) -> None:
        raise NotImplementedError()

    # Module structure

    def visit_import(self, o: Import) -> None:
        raise NotImplementedError()

    def visit_import_from(self, o: ImportFrom) -> None:
        raise NotImplementedError()

    def visit_import_all(self, o: ImportAll) -> None:
        raise NotImplementedError()

    # Statements

    def visit_block(self, o: Block) -> None:
        for s in o.body:
            s.accept(self)

    def visit_expression_stmt(self, o: ExpressionStmt) -> None:
        raise NotImplementedError()

    def visit_operator_assignment_stmt(self, o: OperatorAssignmentStmt) -> None:
        raise NotImplementedError()

    def in_scope_vars(
        self, vars: Dict[str, Expr], types: Dict[MypyExpr, MypyType]
    ) -> Set[MypyVar]:
        r = set()
        for v in vars:
            for k, t in types.items():
                if isinstance(k, NameExpr) and k.name == v:
                    r.add((v, t))
        return r

    def visit_while_stmt(self, o: WhileStmt) -> None:
        v = RWVarsVisitor(self.types)
        o.accept(v)

        writes = list(v.writes)
        writes.sort()

        reads = list(v.reads)
        reads.sort()

        in_scope = list(self.in_scope_vars(self.state.vars, self.types))
        in_scope.sort()

        print(f"loop writes: {writes}, reads: {reads}, scope: {in_scope}")

        assert None not in self.fn_type.arg_names
        formals = list(
            zip(cast(List[str], self.fn_type.arg_names), self.fn_type.arg_types)
        )

        inv = self.pred_tracker.invariant(
            self.fn_name, o, formals, writes, reads, in_scope, self.inv_grammar
        )
        self.invariants[o] = inv

        # inv is true on loop entry
        self.state.asserts.append(
            Implies(And(*self.state.precond), inv.call(self.state))
            if self.state.precond
            else inv.call(self.state)
        )
        print(f"inv is init true: {self.state.asserts[-1]}")

        # havoc the modified vars
        for var in v.writes:
            new_value = self.var_tracker.variable(var[0], to_mltype(var[1]))
            self.state.write(var[0], new_value)
            # print(f"havoc: {var[0]} -> {new_value}")

        body_visitor = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.fn_name,
            self.fn_type,
            self.ast,
            self.args,
            self.ret_val,
            copy.deepcopy(self.state),
            self.invariants,
            self.var_tracker,
            self.pred_tracker,
            self.inv_grammar,
            self.ps_grammar,
            self.types,
        )
        o.body.accept(body_visitor)

        # inv is preserved
        cond = o.expr.accept(self)
        c = (
            And(*self.state.precond, cond, inv.call(self.state))
            if self.state.precond
            else And(cond, inv.call(self.state))
        )
        self.state.asserts.append(Implies(c, inv.call(body_visitor.state)))
        print(f"inv is preserved: {self.state.asserts[-1]}")

        # the invariant is true from this point on
        self.state.precond.append(And(Not(cond), inv.call(self.state)))

    def visit_return_stmt(self, o: ReturnStmt) -> None:
        assert o.expr is not None
        # precond -> ps(...)
        ps = Call(
            self.pred_tracker.predicates[self.ast].name,
            Bool(),
            *self.args,
            o.expr.accept(self),
        )
        if self.state.precond:
            cond = (
                And(*self.state.precond)
                if len(self.state.precond) > 1
                else self.state.precond[0]
            )
            self.state.asserts.append(Implies(cond, ps))
        else:
            self.state.asserts.append(ps)

        print(f"ps: {self.state.asserts[-1]}")
        self.state.has_returned = True

    def visit_assert_stmt(self, o: AssertStmt) -> None:
        raise NotImplementedError()

    def visit_if_stmt(self, o: IfStmt) -> None:
        assert len(o.expr) == 1  # not sure why it is a list
        cond = o.expr[0].accept(self)
        print(f"if stmt with cond {cond}")

        # clone the current state
        c_state = copy.deepcopy(self.state)
        c_state.precond.append(cond)
        consequent = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.fn_name,
            self.fn_type,
            self.ast,
            self.args,
            self.ret_val,
            c_state,
            self.invariants,
            self.var_tracker,
            self.pred_tracker,
            self.inv_grammar,
            self.ps_grammar,
            self.types,
        )
        a_state = copy.deepcopy(self.state)
        a_state.precond.append(Not(cond))
        alternate = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.fn_name,
            self.fn_type,
            self.ast,
            self.args,
            self.ret_val,
            a_state,
            self.invariants,
            self.var_tracker,
            self.pred_tracker,
            self.inv_grammar,
            self.ps_grammar,
            self.types,
        )

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
        else:  # both have not returned, need to merge
            for v in set().union(c_state.vars, a_state.vars):
                if v not in self.state.vars and (
                    (v not in c_state.vars and v in a_state.vars)
                    or (v in c_state.vars and v not in a_state.vars)
                ):
                    raise RuntimeError(f"{v} only in one of the branches for ite {o}")

            # at this point we know that all vars exist in both c_state and a_state
            for v, c_e in c_state.vars.items():
                a_e = a_state.vars[v]
                if c_e != a_e:
                    self.state.vars[v] = Ite(cond, c_e, a_e)
                else:
                    self.state.vars[v] = c_e

            print(f"merged state: {self.state.vars}")

    def visit_break_stmt(self, o: BreakStmt) -> None:
        raise NotImplementedError()

    def visit_continue_stmt(self, o: ContinueStmt) -> None:
        raise NotImplementedError()

    def visit_pass_stmt(self, o: PassStmt) -> None:
        raise NotImplementedError()

    def visit_raise_stmt(self, o: RaiseStmt) -> None:
        raise NotImplementedError()

    def visit_try_stmt(self, o: TryStmt) -> None:
        raise NotImplementedError()

    def visit_match_stmt(self, o: MatchStmt) -> None:
        raise NotImplementedError()

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
            e = e and self.process_comparison(
                o.operators[i], operands[i], operands[i + 1]
            )
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
            raise NotImplementedError(f"Division not supported in {o}")
        elif op == "%":
            raise NotImplementedError(f"Modulo not supported in {o}")
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


class Driver:
    var_tracker: VariableTracker
    inv_tracker: PredicateTracker
    asserts: List[Expr]
    postconditions: List[Expr]
    fns: Dict[str, "MetaliftFunc"]  # maps analyzed function names to returned object
    target_fn: Callable[[], List[FnDecl]]

    def __init__(self) -> None:
        self.var_tracker = VariableTracker()
        self.inv_tracker = PredicateTracker()
        self.asserts = []
        self.postconditions = []
        self.fns = dict()

    def variable(self, name: str, type: MLType) -> Var:
        return self.var_tracker.variable(name, type)

    def analyze(
        self,
        filepath: str,
        fn_name: str,
        target_lang_fn: Callable[[], List[FnDecl]],
        inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> "MetaliftFunc":
        f = MetaliftFunc(
            self, filepath, fn_name, target_lang_fn, inv_grammar, ps_grammar
        )
        self.fns[fn_name] = f
        return f

    # def synthesize_invariants(self,
    #                           grammar_fn: Callable[[Var, WhileStmt, Set[Var], Set[Var], Set[Var]], Expr]) -> None:
    #     for (o, inv) in self.inv_tracker.predicates.items():
    #         writes = [self.var_tracker.variable(v[0], to_mltype(v[1])) for v in inv.writes]
    #         reads = [self.var_tracker.variable(v[0], to_mltype(v[1])) for v in inv.reads]
    #         in_scope = [self.var_tracker.variable(v[0], to_mltype(v[1])) for v in inv.in_scope]
    #         v_exprs = [grammar_fn(v, o, writes, reads, in_scope) for v in writes]
    #         body = And(*v_exprs) if len(v_exprs) > 1 else v_exprs[0]
    #         inv.synth_fn = Synth(inv.name, body, *(writes + reads + in_scope))

    def synthesize(self) -> None:
        synths = [i.gen_Synth() for i in self.inv_tracker.predicates.values()]

        print("asserts: %s" % self.asserts)
        vc = And(*self.asserts)

        target = []
        for fn in self.fns.values():
            target += fn.target_lang_fn()

        synthesized: List[FnDeclRecursive] = run_synthesis(
            "test", target, set(self.var_tracker.all()), synths, [], vc, synths, "cvc5"
        )

        for f in synthesized:
            m = re.match("(\w+)_ps", f.name())  # ignore the invariants
            if m:
                name = m.groups()[0]
                if isinstance(f.body(), Eq):
                    self.fns[name].synthesized = cast(Eq, f.body()).e2()
                    print(f"{name} synthesized: {self.fns[name].synthesized}")
                else:
                    raise Exception(
                        f"synthesized fn body doesn't have form val = ...: {f.body()}"
                    )

    def add_precondition(self, e: Expr) -> None:
        # this gets propagated to the State when it is created
        self.postconditions.append(e)


class MetaliftFunc:
    driver: Driver
    ast: FuncDef
    types: Dict[MypyExpr, MypyType]
    name: str
    target_lang_fn: Callable[[], List[FnDecl]]
    inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    synthesized: Optional[Expr]

    def __init__(
        self,
        driver: Driver,
        filepath: str,
        name: str,
        target_lang_fn: Callable[[], List[FnDecl]],
        inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> None:
        self.driver = driver

        modulename: str = "metalift"
        r = parse(filepath, modulename)  # modulename doesn't really matter?
        # print("r: %s" % r.graph[modulename].tree)

        tree: MypyFile = cast(
            MypyFile, r.graph[modulename].tree
        )  # tree of the entire module / file
        assert tree is not None

        for o in tree.defs:
            if isinstance(o, FuncDef) and o.name == name:
                self.ast = o
                break
        assert self.ast is not None

        self.types = r.types
        self.name = name
        self.target_lang_fn = target_lang_fn
        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar
        self.synthesized = None

    def __call__(self, *args: Any, **kwds: Any) -> Any:
        # set up new state for the call: should contain all global vars and all postconditions
        # from previous invocations
        state = State()
        state.precond += self.driver.postconditions

        v = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.name,
            cast(CallableType, self.ast.type),
            self.ast,
            list(args),
            None,
            state,
            dict(),
            self.driver.var_tracker,
            self.driver.inv_tracker,
            self.inv_grammar,
            self.ps_grammar,
            self.types,
        )

        self.ast.accept(v)
        self.driver.asserts += v.state.asserts

        ret_val = self.driver.var_tracker.variable(
            f"{self.name}_rv", to_mltype(cast(CallableType, self.ast.type).ret_type)
        )

        ps = Call(f"{self.name}_ps", Bool(), ret_val, *args)

        self.driver.postconditions.append(ps)

        return ret_val

    T = TypeVar("T")

    def codegen(self, codegen_fn: Callable[[Expr], T]) -> T:
        if self.synthesized is None:
            raise Exception(f"{self.name} is not synthesized yet")
        else:
            return codegen_fn(self.synthesized)


# def old_main():
#     filename = "tests/python/add.py" if len(sys.argv) == 1 else sys.argv[1]

#     driver = Driver()
#     test = driver.analyze(filename, "test")

#     i = driver.var_tracker.variable("i", Int())
#     r = test(i)

#     # r2 = test(r)

#     driver.synthesize_invariants(inv_grammar)

#     num_runs = 1
#     # ps: y = x or y = 0
#     # candidate = driver.synthesize(Eq(r, retval_grammar(i, num_runs)))
#     candidate = driver.synthesize(Or(Eq(r, i), Eq(r, IntLit(0))))

#     # r = i
#     # num_runs = 4
#     # for x in range(num_runs):
#     #     r = test(r)  # test returns r+r, so this is equivalent to calculating (i * 2^num_runs)

#     # candidate = driver.synthesize(Eq(r, retval_grammar(i, num_runs)))

#     # codegen(candidate[0])

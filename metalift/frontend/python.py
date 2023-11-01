import copy
import re
from typing import (Any, Callable, Dict, List, Literal, Optional, Set, Tuple,
                    Type, TypeVar, Union, cast)

from mypy import build
from mypy.build import BuildResult
from mypy.defaults import PYTHON3_VERSION
from mypy.modulefinder import BuildSource
from mypy.nodes import (AssertStmt, AssignmentStmt, Block, BreakStmt, CallExpr,
                        ClassDef, ComparisonExpr, ContinueStmt, Decorator,
                        DelStmt)
from mypy.nodes import Expression as MypyExpr
from mypy.nodes import (ExpressionStmt, ForStmt, FuncDef, GlobalDecl, IfStmt,
                        Import, ImportAll, ImportFrom, IndexExpr, IntExpr,
                        ListExpr, MatchStmt, MypyFile, NameExpr, NonlocalDecl,
                        OperatorAssignmentStmt, OpExpr, OverloadedFuncDef,
                        PassStmt, RaiseStmt, ReturnStmt, Statement, TryStmt,
                        TupleExpr, UnaryExpr, WhileStmt, WithStmt)
from mypy.options import Options
from mypy.traverser import TraverserVisitor
from mypy.types import CallableType, Instance
from mypy.types import Type as MypyType
from mypy.types import UnboundType
from mypy.visitor import ExpressionVisitor, StatementVisitor
from metalift.analysis_new import VariableTracker
from metalift.synthesize_auto import synthesize as run_synthesis  # type: ignore

from metalift.analysis_new import VariableTracker
from metalift.frontend.utils import ExprSet
from metalift.ir import (And, BoolObject, Call, Eq, Expr, FnDecl,
                         FnDeclRecursive, Ge, Gt, Implies, IntLit, IntObject,
                         Ite, Le, ListObject, Lt, NewObject, Not, Or,
                         SetObject, Sub, Synth, is_list_type, is_set_type, is_tuple_type)
from metalift.ir import Tuple as MLTuple
from metalift.ir import TupleGet, TupleObject
from metalift.ir import Type as MLType
from metalift.ir import (Var, call, create_object, get_object_exprs, implies,
                         is_list_type_expr, is_set_type_expr,
                         is_tuple_type_expr, ite, make_tuple)
from metalift.mypy_util import (get_fn_name, is_func_call,
                                is_func_call_with_name,
                                is_method_call_with_name)
from metalift.synthesize_auto import \
    synthesize as run_synthesis  # type: ignore
from metalift.vc_util import and_exprs, and_objects

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
    precond: List[NewObject]
    vars: Dict[str, NewObject]
    asserts: List[Expr]
    has_returned: bool

    def __init__(
        self,
        precond: List[NewObject] = list(),
        vars: Dict[str, NewObject] = dict(),
        asserts: List[NewObject] = list(),
        has_returned: bool = False,
    ) -> None:
        self.precond = precond
        self.vars = vars
        self.asserts = asserts
        self.has_returned = has_returned if not has_returned else has_returned

    def read(self, var: str) -> NewObject:
        if var in self.vars:
            return self.vars[var]
        raise RuntimeError(f"{var} not found in {self.vars}")

    def write(self, var: str, val: NewObject) -> None:
        self.vars[var] = val


def to_object_type(t: MypyType) -> Type[NewObject]:
    # user annotated types
    if isinstance(t, UnboundType) and t.name == "int":
        return IntObject

    # inferred types
    elif isinstance(t, Instance):
        if t.type.fullname == "builtins.int":
            return IntObject
        elif (
            t.type.fullname == "builtins.list"
            and len(t.args) == 1
            and to_object_type(t.args[0]) == IntObject
        ):
            return ListObject[IntObject]
        elif (
            t.type.fullname == "builtins.set"
            and len(t.args) == 1
            and to_object_type(t.args[0]) == IntObject
        ):
            return SetObject[IntObject]
        else:
            raise RuntimeError(f"unknown Mypy type: {t}")
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

    def _write_name_expr(self, o: NameExpr) -> None:
        t = self.types.get(o)
        assert t is not None
        self.writes.add((o.name, t))

    def visit_assignment_stmt(self, o: AssignmentStmt) -> None:
        if len(o.lvalues) > 1:
            raise RuntimeError(f"multi assignments not supported: {o}")
        lval = cast(
            NameExpr, o.lvalues[0]
        )  # XXX lvalues is a list of Lvalue which can also be indexes or tuples
        self._write_name_expr(lval)

        o.rvalue.accept(self)

    # getting here means we are visiting the RHS of an assignment or a general read only expr
    def visit_name_expr(self, o: NameExpr) -> None:
        t = self.types.get(o)
        assert t is not None
        self.reads.add((o.name, t))

    def visit_call_expr(self, o: CallExpr) -> None:
        # If it is a list append, set add, or set remove call on a variable, then the variable is modified
        if (
            is_method_call_with_name(o, "append")
            or is_method_call_with_name(o, "add")
            or is_method_call_with_name(o, "remove")
        ):
            callee_expr = o.callee.expr  # type: ignore
            if isinstance(callee_expr, NameExpr):
                self._write_name_expr(callee_expr)

        # If it is a function call, then we don't want to evaluate the function type
        if not is_func_call(o):
            o.callee.accept(self)
        for a in o.args:
            a.accept(self)


class Predicate:
    args: List[NewObject]
    writes: List[NewObject]
    reads: List[NewObject]
    in_scope: List[NewObject]
    name: str
    grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    ast: Union[WhileStmt, FuncDef]
    synth: Optional[Synth]

    # argument ordering convention:
    # original arguments of the fn first in its original order, then vars that are in scope
    # and not one of the original arguments in sorted order
    def __init__(
        self,
        ast: Union[WhileStmt, FuncDef],
        args: List[NewObject],
        writes: List[NewObject],
        reads: List[NewObject],
        in_scope: List[NewObject],
        name: str,
        grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
    ) -> None:
        self.args = args
        self.writes = writes
        self.reads = reads
        self.in_scope = in_scope
        self.name = name
        self.grammar = grammar
        self.ast = ast
        self.synth = None

    def call(self, state: State) -> BoolObject:
        return call(self.name, BoolObject, *[state.read(v.var_name()) for v in self.args])

    def gen_Synth(self) -> Synth:
        v_objects = [self.grammar(v, self.writes, self.reads, self.in_scope) for v in self.writes]
        body = and_exprs(*get_object_exprs(v_objects))
        return Synth(self.name, body, *self.args)


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
        args: List[NewObject],
        writes: List[NewObject],
        reads: List[NewObject],
        in_scope: List[NewObject],
        grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
    ) -> Predicate:
        if o in self.predicates:
            return self.predicates[o]
        else:
            non_args_scope_vars = list(ExprSet(in_scope) - ExprSet(args))
            non_args_scope_vars.sort(key=lambda obj: obj.var_name())
            args = (
                args + non_args_scope
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
        grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
    ) -> Predicate:
        if o in self.predicates:
            return self.predicates[o]
        else:
            ps = Predicate(o, ins + outs, outs, ins, [], f"{o.name}_ps", grammar)
            self.predicates[o] = ps
            return ps

    def call(self, o: WhileStmt, s: State) -> Bool:
        return self.predicates[o].call(s)


class VCVisitor(StatementVisitor[None], ExpressionVisitor[Object]):

    driver: "Driver"
    fn_name: str
    fn_type: CallableType
    ast: FuncDef
    args: List[NewObject]
    ret_val: Optional[NewObject]  # remove

    state: State
    invariants: Dict[WhileStmt, Predicate]

    var_tracker: VariableTracker
    pred_tracker: PredicateTracker

    inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]

    types: Dict[MypyExpr, MypyType]

    uninterp_fns: List[str]

    def __init__(
        self,
        driver: "Driver",
        fn_name: str,
        fn_type: CallableType,
        ast: FuncDef,
        args: List[NewObject],
        ret_val: Optional[NewObject],
        state: State,
        invariants: Dict[WhileStmt, Predicate],
        var_tracker: VariableTracker,
        pred_tracker: PredicateTracker,
        inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        types: Dict[MypyExpr, MypyType],
        uninterp_fns: List[str],
    ) -> None:
        self.driver = driver
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
        self.uninterp_fns = uninterp_fns

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
                self.fn_name, to_object_type(fn_type.ret_type)
            )
            self.ast = o

            arg_names = cast(List[str], fn_type.arg_names)
            formals = list(zip(arg_names, fn_type.arg_types))

            if len(fn_type.arg_names) != len(self.args):
                raise RuntimeError(
                    f"expect {len(fn_type.arg_names)} args passed to {self.fn_name} got {len(self.args)} instead"
                )

            for actual, formal in zip(self.args, formals):
                if to_object_type(formal[1]) != actual.type:
                    raise RuntimeError(
                        f"expect {actual} to have type {to_object_type(formal[1])} rather than {actual.type}"
                    )
                self.state.write(formal[0], actual)

            if fn_type.ret_type is None:
                raise RuntimeError(f"fn must return a value: {fn_type}")

            # self.pred_tracker.postcondition(
            #     o, [(self.fn_name, fn_type.ret_type)], formals, self.ps_grammar
            # )
            object_type = to_object_type(self.fn_type.ret_type)
            return_arg = create_object(object_type, f"{self.fn_name}_rv")
            self.pred_tracker.postcondition(
                o,
                [return_arg],
                self.args,
                self.ps_grammar,
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
        o.expr.accept(self)

    def visit_operator_assignment_stmt(self, o: OperatorAssignmentStmt) -> None:
        raise NotImplementedError()

    def in_scope_vars(
        self, vars: Dict[str, NewObject], types: Dict[MypyExpr, MypyType]
    ) -> Set[MypyVar]:
        r = set()
        for v in vars.keys():
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

        write_objects = [
            create_object(to_object_type(type), name)
            for name, type
            in writes
        ]
        read_objects = [
            create_object(to_object_type(type), name)
            for name, type
            in reads
        ]
        in_scope_objects = [
            create_object(to_object_type(type), name)
            for name, type
            in in_scope
        ]
        inv = self.pred_tracker.invariant(
            fn_name=self.fn_name,
            o=o,
            args=self.args,
            writes=write_objects,
            reads=read_objects,
            in_scope=in_scope_objects,
            grammar=self.inv_grammar
        )
        self.invariants[o] = inv

        # inv is true on loop entry
        self.state.asserts.append(
            implies(and_objects(*self.state.precond), inv.call(self.state))
            if self.state.precond
            else inv.call(self.state)
        )
        print(f"inv is init true: {self.state.asserts[-1]}")

        # havoc the modified vars
        for var in v.writes:
            new_value = create_object(to_object_type(var[1]), var[0])
            self.driver.add_var_object(new_value)
            self.state.write(var[0], new_value)

        body_visitor = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.driver,
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
            self.uninterp_fns,
        )
        o.body.accept(body_visitor)

        # inv is preserved
        cond = o.expr.accept(self)
        # if not isinstance(cond, Bool):
        #     raise Exception(
        #         "The condition of a while loop must evaluate to a boolean object!"
        #     )
        c = (
            and_objects(*self.state.precond, cond, inv.call(self.state))
            if self.state.precond
            else and_objects(cond, inv.call(self.state))
        )
        self.state.asserts.append(implies(c, inv.call(body_visitor.state)))
        print(f"inv is preserved: {self.state.asserts[-1]}")

        # the invariant is true from this point on
        self.state.precond.append(and_objects(cond.Not(), inv.call(self.state)))

    def visit_return_stmt(self, o: ReturnStmt) -> None:
        assert o.expr is not None
        # precond -> ps(...)
        ps = call(
            self.pred_tracker.predicates[self.ast].name,
            BoolObject,
            *self.args,
            o.expr.accept(self),
        )
        ps = cast(Bool, ps)
        if self.state.precond:
            cond = (
                and_objects(*self.state.precond)
                if len(self.state.precond) > 1
                else self.state.precond[0]
            )
            self.state.asserts.append(implies(cond, ps))
        else:
            self.state.asserts.append(ps)

        print(f"ps: {self.state.asserts[-1]}")
        self.state.has_returned = True

    def visit_assert_stmt(self, o: AssertStmt) -> None:
        raise NotImplementedError()

    def visit_if_stmt(self, o: IfStmt) -> None:
        assert len(o.expr) == 1  # not sure why it is a list
        cond = o.expr[0].accept(self)
        if not isinstance(cond, Bool):
            raise Exception(
                "The condition of an if loop must evaluate to a bool object!"
            )
        print(f"if stmt with cond {cond}")

        # clone the current state
        c_state = copy.deepcopy(self.state)
        c_state.precond.append(cond)
        consequent = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.driver,
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
            self.uninterp_fns,
        )
        a_state = copy.deepcopy(self.state)
        a_state.precond.append(cond.Not())
        alternate = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.driver,
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
            self.uninterp_fns,
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
                    self.state.vars[v] = ite(cond, c_e, a_e)
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
    def visit_int_expr(self, o: IntExpr) -> IntObject:
        return IntObject(o.value)

    def visit_name_expr(self, o: NameExpr) -> IntObject:
        return self.state.read(o.name)

    # a < b < c is equiv to a < b and b < c
    def visit_comparison_expr(self, o: ComparisonExpr) -> BoolObject:
        operands = [e.accept(self) for e in o.operands]
        e = self.process_comparison(o.operators[0], operands[0], operands[1])
        for i in range(1, len(o.operators)):
            e = e and self.process_comparison(
                o.operators[i], operands[i], operands[i + 1]
            )
        return e

    # ">" | "<" | "==" | ">=" | "<=" | "!=" | "is" ["not"] | ["not"] "in"
    def process_comparison(self, op: str, left: NewObject, right: NewObject) -> NewObject:
        if op == ">":
            return left > right
        elif op == "<":
            return left < right
        elif op == "==":
            return left == right
        elif op == ">=":
            return left >= right
        elif op == "<=":
            return left <= right
        else:
            raise RuntimeError(f"NYI: {op}")

    # binary expr
    def visit_op_expr(self, o: OpExpr) -> NewObject:
        l = o.left.accept(self)
        r = o.right.accept(self)
        op = o.op
        if op in {"+", "-", "*"}:
            if not isinstance(l, Int) or not isinstance(r, Int):
                raise Exception(f"{op} is only supported for int objects!")
        if op in {"and", "or"}:
            if not isinstance(l, Bool) or not isinstance(r, Bool):
                raise Exception(f"{op} is only supported for bool objects!")
        if op == "+":
            return l + r  # type: ignore
        elif op == "-":
            return l - r  # type: ignore
        elif op == "*":
            return l * r  # type: ignore
        elif op == "//":
            return l // r  # type: ignore
        elif op == "/":
            raise NotImplementedError(f"Division not supported in {o}")
        elif op == "%":
            raise NotImplementedError(f"Modulo not supported in {o}")
        elif op == "and":
            return l.And(r)
        elif op == "or":
            return l.Or(r)
        else:
            raise RuntimeError(f"unknown binary op: {op} in {o}")


    def visit_tuple_expr(self, o: TupleExpr) -> MLTuple:
        tuple_exprs = [expr.accept(self) for expr in o.items]
        return make_tuple(*tuple_exprs)

    def visit_index_expr(self, o: IndexExpr) -> Expr:
        # Currently only supports indexing into tuples and lists using integers
        index = o.index.accept(self)
        base = o.base.accept(self)
        if index.type != IntObject:
            raise Exception("Index must be int!")
        if is_tuple_type(base.type):
            return base[index]
        if is_list_type(base.type):
            return base[index]
        raise Exception("Can only index into tuples and lists!")

    def visit_list_expr(self, o: ListExpr) -> Object:
        if len(o.items) > 0:
            raise Exception("Initialization of non-empty lists is not supported!")
        return ListObject[IntObject].empty(IntObject)

    def visit_unary_expr(self, o: UnaryExpr) -> Object:
        if o.op == "-":
            expr = o.expr.accept(self)
            if expr.type != IntObject:
                raise Exception("Unary operator '-' only supported on integers!")
            return 0 - expr
        raise Exception(f"Unsupported unary operator '{o.op}'")

    def visit_call_expr(self, o: CallExpr) -> Object:
        if is_func_call_with_name(o, "len"):
            assert len(o.args) == 1
            arg = o.args[0].accept(self)
            if not is_list_type(arg.type):
                raise Exception("len only supported on lists!")
            return arg.len()
        elif is_method_call_with_name(o, "append"):
            # list append
            callee_expr = o.callee.expr.accept(self)  # type: ignore
            if not is_list_type(callee_expr.type):
                raise Exception(".append only supported on lists!")
            assert len(o.args) == 1
            elem_to_append = o.args[0].accept(self)
            var_name = callee_expr.var_name()
            list_after_append = callee_expr.append(elem_to_append)
            self.state.write(var_name, list_after_append)
            return list_after_append
        elif is_method_call_with_name(o, "add") or is_method_call_with_name(
            o, "remove"
        ):
            # set add or set remove
            if is_method_call_with_name(o, "add"):
                method_name, func_call_name = ".add", "set-union"
            else:
                method_name, func_call_name = ".remove", "set-minus"

            callee_expr = o.callee.expr.accept(self)  # type: ignore
            if not is_set_type(callee_expr.type):
                raise Exception(f"{method_name} only supported on sets!")
            assert len(o.args) == 1
            elem = o.args[0].accept(self)
            singleton_set = SetObject[elem.type].singleton(elem)
            set_after_modification = call(
                func_call_name, callee_expr.type, callee_expr, singleton_set
            )
            self.state.write(callee_expr.var_name(), set_after_modification)
            return set_after_modification
        elif is_func_call(o) and get_fn_name(o) in self.uninterp_fns:
            # Uninterpreted functions
            args = [a.accept(self) for a in o.args]
            expr_type = self.types.get(o)
            assert expr_type is not None
            return call(get_fn_name(o), to_object_type(expr_type), *args)
        raise Exception("Unrecognized call expression!")


class Driver:
    var_tracker: VariableTracker
    inv_tracker: PredicateTracker
    asserts: List[BoolObject]
    postconditions: List[BoolObject]
    fns: Dict[str, "MetaliftFunc"]  # maps analyzed function names to returned object
    target_fn: Callable[[], List[FnDecl]]
    fns_synths: List[Synth]
    uninterp_fns: List[str]

    def __init__(self) -> None:
        self.var_tracker = VariableTracker()
        self.inv_tracker = PredicateTracker()
        self.asserts = []
        self.postconditions = []
        self.fns = dict()
        self.fns_synths = []
        self.uninterp_fns = []

    def variable(self, name: str, type: ObjectT) -> Var:
        return self.var_tracker.variable(name, type)

    def add_var_object(self, var_object: NewObject) -> None:
        # TODO(jie): extract this check to a more generic function
        if not isinstance(var_object.src, Var):
            raise Exception("source is not variable!")
        self.var_tracker.variable(var_object.var_name(), var_object.src.type)

    def add_var_objects(self, var_objects: List[NewObject]) -> None:
        for var_object in var_objects:
            self.add_var_object(var_object)

    def analyze(
        self,
        filepath: str,
        fn_name: str,
        target_lang_fn: Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
        inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        uninterp_fns: List[str] = [],
    ) -> "MetaliftFunc":
        f = MetaliftFunc(
            driver=self,
            filepath=filepath,
            name=fn_name,
            target_lang_fn=target_lang_fn,
            inv_grammar=inv_grammar,
            ps_grammar=ps_grammar,
            uninterp_fns=uninterp_fns,
        )
        self.fns[fn_name] = f
        return f

    def synthesize(self) -> None:
        synths = [i.gen_Synth() for i in self.inv_tracker.predicates.values()]

        print("asserts: %s" % self.asserts)
        vc = and_objects(*self.asserts).src

        target = []
        for fn in self.fns.values():
            target += fn.target_lang_fn()

        synthesized: List[FnDeclRecursive] = run_synthesis(
            basename="test",
            targetLang=target,
            vars=set(self.var_tracker.all()),
            invAndPs=synths + self.fns_synths,
            preds=[],
            vc=vc,
            loopAndPsInfo=synths,  # TODO: does this need fns synths
            cvcPath="cvc5",
            uninterp_fns=self.uninterp_fns,
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

    def add_precondition(self, e: BoolObject) -> None:
        # this gets propagated to the State when it is created
        self.postconditions.append(e)


class MetaliftFunc:
    driver: Driver
    ast: FuncDef
    types: Dict[MypyExpr, MypyType]
    name: str
    target_lang_fn: Callable[[], List[Union[FnDecl, FnDeclRecursive]]]
    inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    synthesized: Optional[Expr]
    uninterp_fns: List[str]

    def __init__(
        self,
        driver: Driver,
        filepath: str,
        name: str,
        target_lang_fn: Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
        inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        uninterp_fns: List[str],
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
        self.uninterp_fns = uninterp_fns

    def __call__(self, *args: Any, **kwds: Any) -> Any:
        # set up new state for the call: should contain all global vars and all postconditions
        # from previous invocations
        state = State()
        state.precond += self.driver.postconditions

        v = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            self.driver,
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
            self.uninterp_fns,
        )

        self.ast.accept(v)
        self.driver.asserts += v.state.asserts

        object_type = to_object_type(cast(CallableType, self.ast.type).ret_type)
        ret_val = create_object(object_type, f"{self.name}_rv")
        self.driver.add_var_object(ret_val)

        ps = call(f"{self.name}_ps", BoolObject, ret_val, *args)

        self.driver.postconditions.append(cast(Bool, ps))

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

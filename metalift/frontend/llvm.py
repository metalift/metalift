from collections import defaultdict
import re
from typing import Any, Callable, Dict, List, Optional, Set, Tuple, TypeVar, Union, cast
from metalift.analysis_new import RawBlock, VariableTracker
from metalift.synthesize_auto import synthesize as run_synthesis  # type: ignore
from llvmlite import binding as llvm
from llvmlite import ir as llvm_ir

from metalift.ir import (
    Add,
    And,
    Bool,
    BoolLit,
    Call,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    FnT,
    Ge,
    Gt,
    Implies,
    Int,
    IntLit,
    Ite,
    Le,
    ListT,
    Lit,
    Lt,
    Mul,
    Not,
    Object,
    Or,
    Pointer,
    SetT,
    Sub,
    Synth,
    Tuple as MLTuple,
    TupleGet,
    TupleT,
    Type as MLType,
    Var,
    parseTypeRef,
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
    BreakStmt,
    ClassDef,
    ComparisonExpr,
    ContinueStmt,
    Decorator,
    DelStmt,
    Expression as ValueRef,
    ExpressionStmt,
    ForStmt,
    FuncDef,
    GlobalDecl,
    IfStmt,
    Import,
    ImportAll,
    ImportFrom,
    IntExpr,
    IndexExpr,
    MatchStmt,
    MypyFile,
    NameExpr,
    NonlocalDecl,
    OperatorAssignmentStmt,
    OpExpr,
    OverloadedFuncDef,
    PassStmt,
    RaiseStmt,
    ReturnStmt,
    Statement,
    TryStmt,
    TupleExpr,
    WhileStmt,
    WithStmt,
)
from mypy.types import CallableType, Instance, Type as TypeRef, UnboundType
from mypy.visitor import ExpressionVisitor, StatementVisitor

import copy

from metalift.analysis import setupBlocks

from metalift.vc import Block

from metalift.vc_util import and_exprs, or_exprs

# Run the interpreted version of mypy instead of the compiled one to avoid
# TypeError: interpreted classes cannot inherit from compiled traits
# from https://github.com/python/mypy
# python3 -m pip install --no-binary mypy -U mypy


def parse(path: str, modulename: str) -> BuildResult:
    options = Options()
    options.incremental = False  # turn off caching of previously typed results
    # options.export_types = Trueref = llvm.parse_assembly
    options.show_traceback = True
    options.python_version = PYTHON3_VERSION
    options.preserve_asts = True
    options.export_types = True
    return build.build(sources=[BuildSource(path, modulename, None)], options=options)


LLVMVar = Tuple[str, TypeRef]


class State:
    precond: List[Expr]
    vars: Dict[str, Expr]
    asserts: List[Expr]
    has_returned: bool
    processed: bool

    def __init__(
        self,
        precond: Optional[List[Expr]] = None,
        vars: Optional[Dict[str, Expr]] = None,
        asserts: Optional[List[Expr]] = None,
        has_returned: bool = False,
    ) -> None:
        self.precond = precond or []
        self.vars = vars or {}
        self.asserts = asserts or []
        self.has_returned = has_returned if not has_returned else has_returned
        self.processed = False

    def read_operand(self, op: ValueRef) -> Expr:
        if op.name:
            return self.read(op.name)

        val = re.search("\w+ (\S+)", str(op)).group(1)  # type: ignore
        if val == "true":
            return Lit(True, Bool())
        elif val == "false":
            return Lit(False, Bool())
        else:  # assuming it's a number
            return Lit(int(val), Int())

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


def to_mltype(t: Union[TypeRef, MLType]) -> MLType:
    if isinstance(t, MLType):
        return t
    # user annotated types
    if isinstance(t, UnboundType) and t.name == "int":
        return Int()

    # inferred types
    elif isinstance(t, Instance) and t.type.fullname == "builtins.int":
        return Int()

    else:
        raise RuntimeError(f"unknown Mypy type: {t}")


class RWVarsVisitor(TraverserVisitor):
    writes: Set[LLVMVar]
    reads: Set[LLVMVar]
    types: Dict[ValueRef, TypeRef]

    def __init__(self, types: Dict[ValueRef, TypeRef]) -> None:
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
    args: List[LLVMVar]
    writes: List[LLVMVar]
    reads: List[LLVMVar]
    in_scope: List[LLVMVar]
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
        args: List[LLVMVar],
        writes: List[LLVMVar],
        reads: List[LLVMVar],
        in_scope: List[LLVMVar],
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

        body = and_exprs(*v_exprs)

        vars = [Var(v[0], to_mltype(v[1])) for v in self.args]
        return Synth(self.name, body, *vars)


class PredicateTracker:
    types: Dict[ValueRef, TypeRef]
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
        args: List[LLVMVar],
        writes: List[LLVMVar],
        reads: List[LLVMVar],
        in_scope: List[LLVMVar],
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
        outs: List[LLVMVar],
        ins: List[LLVMVar],
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
    fn_type: MLType
    fn: ValueRef
    args: List[Expr]
    ret_val: Optional[Expr]  # remove

    state: State
    invariants: Dict[WhileStmt, Predicate]

    var_tracker: VariableTracker
    pred_tracker: PredicateTracker

    inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]

    fn_blocks: Dict[str, Block]
    block_states: Dict[str, State]

    def __init__(
        self,
        fn_name: str,
        fn_type: MLType,
        fn: ValueRef,
        args: List[Expr],
        ret_val: Optional[Expr],
        state: State,
        invariants: Dict[WhileStmt, Predicate],
        var_tracker: VariableTracker,
        pred_tracker: PredicateTracker,
        inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        fn_blocks: Dict[str, Block]
    ) -> None:
        self.fn_name = fn_name
        self.fn_type = fn_type
        self.fn = fn
        self.args = args
        self.ret_val = ret_val

        self.state = state
        self.invariants = invariants
        self.var_tracker = var_tracker
        self.pred_tracker = pred_tracker

        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar

        self.fn_blocks = fn_blocks

        self.block_states: Dict[str, State] = {}


        # TODO: use defaultdict
        for block_name in self.fn_blocks.keys():
            self.block_states[block_name] = State()

    def get_blk_state(self, block_name: str) -> State:
        if block_name not in self.block_states.keys():
            raise Exception(f"Block '{block_name}' does not exist!")
        return self.block_states[block_name]
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

    def visit_initial_llvm_block(self, block: ValueRef) -> None:
        block_state = self.get_blk_state(block.name)
        ret_type: MLType = self.fn_type.args[0]
        arg_types: List[MLType] = self.fn_type.args[1]
        arg_names: List[str] = [a.name() for a in self.args]
        formals = list(zip(arg_names, arg_types))
        self.pred_tracker.postcondition(
            self.fn,
            [(f"{self.fn_name}_rv", ret_type)],
            formals,
            self.ps_grammar,
        )

        if len(list(self.fn.arguments)) != len(self.args):
            raise RuntimeError(
                f"expect {len(arg_names)} args passed to {self.fn_name} got {len(self.args)} instead"
            )

        for actual, formal in zip(self.args, formals):
            if actual.type != formal[1]:
                raise RuntimeError(
                    f"expect {actual} to have type {formal[1]} rather than {actual.type}"
                )
            block_state.write(formal[0], actual)

        if ret_type is None:
            raise RuntimeError(f"fn must return a value: {self.fn_type}")
        block_state.processed = True

        self.visit_instructions(block.name, block.instructions)

    def visit_instruction(self, block_name: str, o: ValueRef) -> None:
        if o.opcode == "alloca":
            self.visit_alloca_instruction(block_name, o)
        elif o.opcode == "load":
            self.visit_load_instruction(block_name, o)
        elif o.opcode == "store":
            self.visit_store_instruction(block_name, o)
        elif o.opcode == "add":
            self.visit_add_instruction(block_name, o)
        elif o.opcode == "sub":
            self.visit_sub_instruction(block_name, o)
        elif o.opcode == "mul":
            self.visit_mul_instruction(block_name, o)
        elif o.opcode == "icmp":
            self.visit_icmp_instruction(block_name, o)
        elif o.opcode == "br":
            self.visit_br_instruction(block_name, o)
        elif o.opcode == "ret":
            self.visit_ret_instruction(block_name, o)
        else:
            print("MISSING SUPPORT FOR INSTRUCTION", o.opcode)

    def merge_states(self, block: ValueRef) -> State:
        if len(block.preds) == 0:
            return
        elif len(block.preds) == 1:
            blk_state = self.get_blk_state(block.name)
            pred_state = self.get_blk_state(block.preds[0].name)
            blk_state.vars = copy.deepcopy(pred_state.vars)
            # TODO: do we need to copy over asserts
            blk_state.asserts = copy.deepcopy(pred_state.asserts)
            blk_state.precond.extend(copy.deepcopy(pred_state.precond))
            blk_state.has_returned = False
            blk_state.processed = False
        else:
            blk_state = self.get_blk_state(block.name)
            # Merge preconditions

            # TODO: do we really need the preconds here
            # for pred in block.preds:
            #     pred_state = self.get_blk_state(pred.name)
            #     if len(pred_state.precond) > 1:
            #         pred_preconds.append(And(*pred_state.precond))
            #     else:
            #         pred_preconds.append(pred_state.precond[0])
            # if len(pred_preconds) > 1:
            #     blk_state.precond = [Or(*pred_preconds)]
            # else:
            #     blk_state.precond = pred_preconds[0]

            # TODO: handle global vars and uninterpreted functions

            # Merge state
            # Mapping from variable (register/arg names) to a mapping from values to assume statements
            var_state: Dict[str, Dict[Expr, List[Expr]]] = defaultdict(lambda: defaultdict(list))
            for pred in block.preds:
                pred_state = self.get_blk_state(pred.name)
                for var_name, var_value in pred_state.vars.items():
                    var_state[var_name][var_value].append(pred_state.precond)

            merged_vars: Dict[str, Expr] = {}
            for var_name, value_to_precond_mapping in var_state.items():
                if len(value_to_precond_mapping) == 1:
                    merged_vars[var_name] = list(value_to_precond_mapping.keys())[0]
                else:
                    value_to_aggregated_precond: Dict[Expr, Expr] = {}
                    for value, all_preconds in value_to_precond_mapping.items():
                        all_aggregated_preconds: List[Expr] = []
                        for preconds in all_preconds:
                            all_aggregated_preconds.append(and_exprs(*preconds))
                        value_to_aggregated_precond[value] = or_exprs(*all_aggregated_preconds)

                    merged_value = None
                    for value, aggregated_precond in value_to_aggregated_precond.items():
                        if merged_value is None:
                            merged_value = value
                        else:
                            merged_value = Ite(aggregated_precond, value, merged_value)
                    merged_vars[var_name] = merged_value
            blk_state.vars = merged_vars
            # TODO: how to handle asserts here?


    def visit_llvm_block(self, block: ValueRef) -> None:
        if len(block.preds) == 0:
            self.visit_initial_llvm_block(block)
        else:
            # First we need to merge states
            self.merge_states(block)
            # TODO: add key checking
            self.visit_instructions(block.name, block.instructions)
            self.get_blk_state(block.name).processed = True

    def visit_instructions(
        self,
        block_name: str,
        instructions: List[ValueRef]
    ) -> None:
        for instr in instructions:
            self.visit_instruction(block_name, instr)

    def visit_alloca_instruction(self, block_name: str, o: ValueRef) -> None:
        # alloca <type>, align <num> or alloca <type>
        t = re.search("alloca ([^$|,]+)", str(o)).group(  # type: ignore
            1
        )  # bug: ops[0] always return i32 1 regardless of type
        if t == "i32":
            val = Lit(0, Int())
        elif t == "i8":
            val = Lit(False, Bool())
        elif t == "i1":
            val = Lit(False, Bool())
        elif t == "%struct.list*":
            val = Lit(0, ListT(Int()))
        elif t.startswith("%struct.set"):
            val = Lit(0, SetT(Int()))
        elif t.startswith("%struct.tup."):
            retType = [Int() for i in range(int(t[-2]) + 1)]
            val = Lit(0, TupleT(*retType))
        elif t.startswith("%struct.tup"):
            val = Lit(0, TupleT(Int(), Int()))
        elif t.startswith(
            "%struct."
        ):  # not a tuple or set, assume to be user defined type
            o = re.search("%struct.(.+)", t)
            if o:
                tname = o.group(1)
            else:
                raise Exception("failed to match struct %s: " % t)

            val = Object(MLType(tname))
        else:
            raise Exception("NYI: %s" % o)

        # o.name is the register name
        self.get_blk_state(block_name).write(o.name, Pointer(val))

    def visit_load_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        ptr_expr = self.get_blk_state(block_name).read(ops[0].name)
        assert ptr_expr.type.name == "Pointer"

        # TODO: change this, this is a bit of a hack.
        if isinstance(ptr_expr, Ite):
            referenced_value = Ite(ptr_expr.c(), ptr_expr.e1().value, ptr_expr.e2().value)
        else:
            referenced_value = ptr_expr.value

        self.get_blk_state(block_name).write(o.name, referenced_value)

    def visit_store_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        value_to_store = self.get_blk_state(block_name).read_operand(ops[0])

        # store into the location stored in ops[1].name
        ptr_expr = self.get_blk_state(block_name).read(ops[1].name)
        assert ptr_expr.type.name == "Pointer"
        ptr_expr.set_value(value_to_store)

    def visit_add_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        add_expr = Add(
            self.get_blk_state(block_name).read_operand(ops[0]),
            self.get_blk_state(block_name).read_operand(ops[1])
        )
        self.get_blk_state(block_name).write(o.name, add_expr)

    def visit_sub_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        sub_expr = Sub(
            self.get_blk_state(block_name).read_operand(ops[0]),
            self.get_blk_state(block_name).read_operand(ops[1])
        )
        self.get_blk_state(block_name).write(o.name, sub_expr)

    def visit_mul_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        mul_expr = Mul(
            self.get_blk_state(block_name).read_operand(ops[0]),
            self.get_blk_state(block_name).read_operand(ops[1])
        )
        self.get_blk_state(block_name).write(o.name, mul_expr)

    def visit_icmp_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        cond = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(o).strip()).group(1)
        # TODO: use parseOperand
        op0 = self.get_blk_state(block_name).read_operand(ops[0])
        op1 = self.get_blk_state(block_name).read_operand(ops[1])

        if cond == "eq":
            value = Eq(op0, op1)
        elif cond == "ne":
            value = Not(Eq(op0, op1))
        elif cond == "sgt":
            value = Gt(op0, op1)
        elif cond == "sle":
            value = Le(op0, op1)
        elif cond == "slt" or cond == "ult":
            value = Lt(op0, op1)
        else:
            raise Exception("NYI %s" % cond)

        self.get_blk_state(block_name).write(o.name, value)

    def visit_br_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        blk_state = self.get_blk_state(block_name)
        if len(ops) > 1:
            # LLVMLite switches the order of branches for some reason
            true_branch = ops[2].name
            false_branch = ops[1].name
            cond = blk_state.read_operand(ops[0])
            self.get_blk_state(true_branch).precond.append(cond)
            self.get_blk_state(false_branch).precond.append(Not(cond))

        return
        ops = list(o.operands)
        blk_state = self.get_blk_state(block_name)
        if len(ops) == 1:
            # Unconditional branch
            next_block = self.fn_blocks[ops[0].name]
            self.visit_instructions(block_name, next_block.instructions)
        else:
            # LLVMLite switches the order of branches for some reason
            true_branch = ops[2].name
            false_branch = ops[1].name
            cond = blk_state.read_operand(ops[0])

            # clone the current state
            c_state = copy.deepcopy(blk_state)
            c_state.precond.append(cond)
            consequent = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
                fn_name=self.fn_name,
                fn_type=self.fn_type,
                fn=self.fn,
                args=self.args,
                ret_val=self.ret_val,
                state=c_state,
                invariants=self.invariants,
                var_tracker=self.var_tracker,
                pred_tracker=self.pred_tracker,
                inv_grammar=self.inv_grammar,
                ps_grammar=self.ps_grammar,
                fn_blocks=self.fn_blocks
            )
            # TODO: finish this
            a_state = copy.deepcopy(blk_state)
            a_state.precond.append(Not(cond))
            alternate = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
                fn_name=self.fn_name,
                fn_type=self.fn_type,
                fn=self.fn,
                args=self.args,
                ret_val=self.ret_val,
                state=c_state,
                invariants=self.invariants,
                var_tracker=self.var_tracker,
                pred_tracker=self.pred_tracker,
                inv_grammar=self.inv_grammar,
                ps_grammar=self.ps_grammar,
                fn_blocks=self.fn_blocks
            )

            true_branch_block = self.fn_blocks[true_branch]
            consequent.visit_instructions(block_name, true_branch_block.instructions)

            false_branch_block = self.fn_blocks[false_branch]
            alternate.visit_instructions(block_name, false_branch_block.instructions)

            # merge
            c_state = consequent.state
            a_state = alternate.state

            for e in c_state.asserts + a_state.asserts:
                if e not in blk_state.asserts:
                    blk_state.asserts.append(e)

            if c_state.has_returned and a_state.has_returned:
                return
            elif c_state.has_returned and not a_state.has_returned:
                blk_state.vars = a_state.vars
            elif not c_state.has_returned and a_state.has_returned:
                blk_state.vars = c_state.vars
            else:  # both have not returned, need to merge
                for v in set().union(c_state.vars, a_state.vars):
                    if v not in blk_state.vars and (
                        (v not in c_state.vars and v in a_state.vars)
                        or (v in c_state.vars and v not in a_state.vars)
                    ):
                        raise RuntimeError(f"{v} only in one of the branches for ite {o}")

                # at this point we know that all vars exist in both c_state and a_state
                for v, c_e in c_state.vars.items():
                    a_e = a_state.vars[v]
                    if c_e != a_e:
                        blk_state.vars[v] = Ite(cond, c_e, a_e)
                    else:
                        blk_state.vars[v] = c_e

                print(f"merged state: {blk_state.vars}")

    def visit_ret_instruction(self, block_name: str, o: ValueRef) -> None:
        # precond -> ps(...)
        # TODO: hanlde ret void
        blk_state = self.get_blk_state(block_name)
        ops = list(o.operands)
        ps = Call(
            self.pred_tracker.predicates[self.fn].name,
            Bool(),
            *self.args,
            blk_state.read_operand(ops[0]),
        )
        if blk_state.precond:
            blk_state.asserts.append(Implies(and_exprs(*blk_state.precond), ps))
        else:
            blk_state.asserts.append(ps)

        print(f"ps: {blk_state.asserts[-1]}")
        blk_state.has_returned = True

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
        self, vars: Dict[str, Expr], types: Dict[ValueRef, TypeRef]
    ) -> Set[LLVMVar]:
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
            Implies(and_exprs(*self.state.precond), inv.call(self.state))
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
            self.fn,
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
            self.pred_tracker.predicates[self.fn].name,
            Bool(),
            *self.args,
            o.expr.accept(self),
        )
        if self.state.precond:
            cond = and_exprs(*self.state.precond)
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
            self.fn,
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
            self.fn,
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

    def visit_tuple_expr(self, o: TupleExpr) -> MLTuple:
        return MLTuple(*[expr.accept(self) for expr in o.items])

    def visit_index_expr(self, o: IndexExpr) -> Expr:
        # Currently only supports indexing into tuples using integers
        index = o.index.accept(self)
        base = o.base.accept(self)
        if index.type != Int():
            raise Exception("Index must be int!")
        if not isinstance(base, MLTuple):
            raise Exception("Can only index into tuples!")
        return TupleGet(o.base.accept(self), o.index.accept(self))


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
        llvm_filepath: str,
        loops_filepath: str,
        fn_name: str,
        target_lang_fn: Callable[[], List[FnDecl]],
        inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> "MetaliftFunc":
        f = MetaliftFunc(
            self,
            llvm_filepath,
            loops_filepath,
            fn_name,
            target_lang_fn,
            inv_grammar,
            ps_grammar
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
        vc = and_exprs(*self.asserts)

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
    fn: ValueRef # TODO jie: should I change this to llvm_ir.Function
    fn_type: MLType
    types: Dict[ValueRef, TypeRef]
    name: str
    target_lang_fn: Callable[[], List[FnDecl]]
    inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    synthesized: Optional[Expr]
    fn_blocks: Dict[str, Block]

    def __init__(
        self,
        driver: Driver,
        llvm_filepath: str,
        loops_filepath: str,
        name: str,
        target_lang_fn: Callable[[], List[FnDecl]],
        inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> None:
        self.driver = driver
        with open(llvm_filepath, mode="r") as file:
            ref = llvm.parse_assembly(file.read())
        self.fn = ref.get_function(name)
        self.fn_blocks = setupBlocks(self.fn.blocks)

        # Find the return type of function
        blocks = {
            block.name: RawBlock(block.name, list(block.instructions))
            for block in self.fn.blocks
        }
        found_return = None
        for block in blocks.values():
            if block.return_type:
                if found_return:
                    assert found_return == block.return_type
                found_return = block.return_type
        return_type = found_return  # type: ignore
        fn_args_types = [parseTypeRef(a.type) for a in self.fn.arguments]
        self.fn_type = FnT(return_type, fn_args_types)

        self.name = name
        self.target_lang_fn = target_lang_fn
        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar
        self.synthesized = None

    def __call__(self, *args: Any, **kwds: Any) -> Any:
        # set up new state for the call: should contain all global vars and all postconditions
        # from previous invocations
        state = State()
        # TODO jie: do I need to anything with this
        state.precond += self.driver.postconditions

        v = VCVisitor(  # type: ignore  # ignore the abstract expr visit methods that aren't implemented for now in VCVisitor
            fn_name=self.name,
            fn_type=self.fn_type,
            fn=self.fn,
            args=list(args),
            ret_val=None,
            state=state,
            invariants=dict(),
            var_tracker=self.driver.var_tracker,
            pred_tracker=self.driver.inv_tracker,
            inv_grammar=self.inv_grammar,
            ps_grammar=self.ps_grammar,
            fn_blocks=self.fn_blocks
        )
        done = False
        while not done:
            done = True
            for b in self.fn_blocks.values():
                if not v.get_blk_state(b.name).processed and (
                    not b.preds or all([v.get_blk_state(p.name).processed for p in b.preds])
                ):
                    v.visit_llvm_block(b)
                    done = False
        # v.visit_func_def(self.fn)
        # self.driver.asserts += v.state.asserts

        ret_val = self.driver.var_tracker.variable(
            f"{self.name}_rv", self.fn_type.args[0]
        )

        ps = Call(f"{self.name}_ps", Bool(), ret_val, *args)

        self.driver.postconditions.append(ps)

        for block in self.fn_blocks.values():
            self.driver.asserts.extend(v.get_blk_state(block.name).asserts)
        # self.driver.asserts += v.state.asserts

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

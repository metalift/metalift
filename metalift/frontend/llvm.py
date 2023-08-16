from collections import defaultdict
import re
from typing import Any, Callable, Dict, Iterable, List, Optional, Set, Tuple, TypeVar, Union, cast
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

# Helper functions
def find_return_type(blocks: Iterable[ValueRef]) -> MLType:
    return_type = None
    for block in blocks:
        final_instruction = block.instructions[-1]
        if final_instruction.opcode == "ret":
            ops = list(final_instruction.operands)
            curr_return_type = parseTypeRef(ops[0].type)
            if return_type is not None and return_type != curr_return_type:
                raise Exception("Return types are not consistent across blocks!")
            return_type = curr_return_type
    if return_type is None:
        raise RuntimeError(f"fn must return a value!")
    return return_type

# TODO: make it namedtuple
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
        writes = [Var(v[0], v[1]) for v in self.writes]
        reads = [Var(v[0], v[1]) for v in self.reads]
        in_scope = [Var(v[0], v[1]) for v in self.in_scope]

        v_exprs = [self.grammar(v, self.ast, writes, reads, in_scope) for v in writes]

        body = and_exprs(*v_exprs)

        vars = [Var(v[0], v[1]) for v in self.args]
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


class VCVisitor:
    fn_name: str
    fn_type: MLType
    fn_ref: ValueRef
    fn_args: List[Expr]
    fn_blocks: Dict[str, Block]
    fn_blocks_states: Dict[str, State]

    state: State
    invariants: Dict[WhileStmt, Predicate]
    var_tracker: VariableTracker
    pred_tracker: PredicateTracker

    inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]
    ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr]

    def __init__(
        self,
        fn_name: str,
        fn_type: MLType,
        fn_ref: ValueRef,
        fn_args: List[Expr],
        fn_blocks: Dict[str, Block],
        state: State,
        invariants: Dict[WhileStmt, Predicate],
        var_tracker: VariableTracker,
        pred_tracker: PredicateTracker,
        inv_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, Statement, List[Var], List[Var], List[Var]], Expr],
    ) -> None:
        self.fn_name = fn_name
        self.fn_type = fn_type
        self.fn_ref = fn_ref
        self.fn_args = fn_args
        self.fn_blocks = fn_blocks
        self.fn_blocks_states: Dict[str, State] = defaultdict(lambda: State())

        self.state = state
        self.invariants = invariants
        self.var_tracker = var_tracker
        self.pred_tracker = pred_tracker

        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar


    # Definitions
    def visit_initial_llvm_block(self, block: ValueRef) -> None:
        blk_state = self.fn_blocks_states[block.name]

        ret_type: MLType = self.fn_type.args[0]
        arg_types: List[MLType] = self.fn_type.args[1]
        arg_names: List[str] = [a.name() for a in self.fn_args]
        formals = list(zip(arg_names, arg_types))
        self.pred_tracker.postcondition(
            self.fn_ref,
            [(f"{self.fn_name}_rv", ret_type)],
            formals,
            self.ps_grammar,
        )

        for arg in self.fn_args:
            blk_state.write(arg.name(), arg)

        self.visit_instructions(block.name, block.instructions)
        blk_state.processed = True

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
            blk_state = self.fn_blocks_states[block.name]
            pred_state = self.fn_blocks_states[block.preds[0].name]
            blk_state.vars = copy.deepcopy(pred_state.vars)
            # TODO: do we need to copy over asserts
            blk_state.asserts = copy.deepcopy(pred_state.asserts)
            blk_state.precond.extend(copy.deepcopy(pred_state.precond))
            blk_state.has_returned = False
            blk_state.processed = False
        else:
            blk_state = self.fn_blocks_states[block.name]
            # Merge preconditions

            # TODO: do we really need the preconds here
            # for pred in block.preds:
            #     pred_state = self.fn_blocks_states[pred.name]
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
                pred_state = self.fn_blocks_states[pred.name]
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
            self.fn_blocks_states[block.name].processed = True

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
        self.fn_blocks_states[block_name].write(o.name, Pointer(val))

    def visit_load_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        ptr_expr = self.fn_blocks_states[block_name].read(ops[0].name)
        assert ptr_expr.type.name == "Pointer"

        # TODO: change this, this is a bit of a hack.
        if isinstance(ptr_expr, Ite):
            referenced_value = Ite(ptr_expr.c(), ptr_expr.e1().value, ptr_expr.e2().value)
        else:
            referenced_value = ptr_expr.value

        self.fn_blocks_states[block_name].write(o.name, referenced_value)

    def visit_store_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        value_to_store = self.fn_blocks_states[block_name].read_operand(ops[0])

        # store into the location stored in ops[1].name
        ptr_expr = self.fn_blocks_states[block_name].read(ops[1].name)
        assert ptr_expr.type.name == "Pointer"
        ptr_expr.set_value(value_to_store)

    def visit_add_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        add_expr = Add(
            self.fn_blocks_states[block_name].read_operand(ops[0]),
            self.fn_blocks_states[block_name].read_operand(ops[1])
        )
        self.fn_blocks_states[block_name].write(o.name, add_expr)

    def visit_sub_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        sub_expr = Sub(
            self.fn_blocks_states[block_name].read_operand(ops[0]),
            self.fn_blocks_states[block_name].read_operand(ops[1])
        )
        self.fn_blocks_states[block_name].write(o.name, sub_expr)

    def visit_mul_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        mul_expr = Mul(
            self.fn_blocks_states[block_name].read_operand(ops[0]),
            self.fn_blocks_states[block_name].read_operand(ops[1])
        )
        self.fn_blocks_states[block_name].write(o.name, mul_expr)

    def visit_icmp_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        cond = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(o).strip()).group(1)
        # TODO: use parseOperand
        op0 = self.fn_blocks_states[block_name].read_operand(ops[0])
        op1 = self.fn_blocks_states[block_name].read_operand(ops[1])

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

        self.fn_blocks_states[block_name].write(o.name, value)

    def visit_br_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        blk_state = self.fn_blocks_states[block_name]
        if len(ops) > 1:
            # LLVMLite switches the order of branches for some reason
            true_branch = ops[2].name
            false_branch = ops[1].name
            cond = blk_state.read_operand(ops[0])
            self.fn_blocks_states[true_branch].precond.append(cond)
            self.fn_blocks_states[false_branch].precond.append(Not(cond))

    def visit_ret_instruction(self, block_name: str, o: ValueRef) -> None:
        # precond -> ps(...)
        # TODO: hanlde ret void
        blk_state = self.fn_blocks_states[block_name]
        ops = list(o.operands)
        ps = Call(
            self.pred_tracker.predicates[self.fn_ref].name,
            Bool(),
            *self.fn_args,
            blk_state.read_operand(ops[0]),
        )
        if blk_state.precond:
            blk_state.asserts.append(Implies(and_exprs(*blk_state.precond), ps))
        else:
            blk_state.asserts.append(ps)

        print(f"ps: {blk_state.asserts[-1]}")
        blk_state.has_returned = True

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
            driver=self,
            llvm_filepath=llvm_filepath,
            loops_filepath=loops_filepath,
            name=fn_name,
            target_lang_fn=target_lang_fn,
            inv_grammar=inv_grammar,
            ps_grammar=ps_grammar
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
    fn_ref: ValueRef # TODO jie: should I change this to llvm_ir.Function
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
        self.fn_ref = ref.get_function(name)
        self.fn_blocks = setupBlocks(self.fn_ref.blocks)

        # Find the return type of function, and set self.fn_type
        return_type = find_return_type(self.fn_blocks.values())
        fn_args_types = [parseTypeRef(a.type) for a in self.fn_ref.arguments]
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

        # Check that the arguments passed in have the same names and types as the function definition.
        if len(list(self.fn_ref.arguments)) != len(args):
            raise RuntimeError(
                f"expect {len(args)} args passed to {self.fn_name} got {len(self.fn_args)} instead"
            )
        for i in range(len(args)):
            fn_ref_args = list(self.fn_ref.arguments)
            passed_in_arg_name, passed_in_arg_type = args[i].name(), args[i].type
            fn_arg_name, fn_arg_type = fn_ref_args[i].name, self.fn_type.args[1][i]
            if passed_in_arg_name != fn_arg_name:
                raise Exception(f"Expecting the {i}th argument to have name {fn_arg_name} but instead got {passed_in_arg_name}")
            if passed_in_arg_type != fn_arg_type:
                raise RuntimeError(
                    f"expect {fn_arg_name} to have type {fn_arg_type} rather than {passed_in_arg_name}"
                )

        v = VCVisitor(
            fn_name=self.name,
            fn_type=self.fn_type,
            fn_ref=self.fn_ref,
            fn_args=list(args),
            fn_blocks=self.fn_blocks,
            state=state,
            invariants=dict(),
            var_tracker=self.driver.var_tracker,
            pred_tracker=self.driver.inv_tracker,
            inv_grammar=self.inv_grammar,
            ps_grammar=self.ps_grammar,
        )
        done = False
        while not done:
            done = True
            for b in self.fn_blocks.values():
                if not v.fn_blocks_states[b.name].processed and (
                    not b.preds or all([v.fn_blocks_states[p.name].processed for p in b.preds])
                ):
                    v.visit_llvm_block(b)
                    done = False

        ret_val = self.driver.var_tracker.variable(
            f"{self.name}_rv", self.fn_type.args[0]
        )

        ps = Call(f"{self.name}_ps", Bool(), ret_val, *args)

        self.driver.postconditions.append(ps)

        for block in self.fn_blocks.values():
            self.driver.asserts.extend(v.fn_blocks_states[block.name].asserts)

        return ret_val

    T = TypeVar("T")

    def codegen(self, codegen_fn: Callable[[Expr], T]) -> T:
        if self.synthesized is None:
            raise Exception(f"{self.name} is not synthesized yet")
        else:
            return codegen_fn(self.synthesized)

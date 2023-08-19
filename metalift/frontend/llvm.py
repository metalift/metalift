from collections import defaultdict
import re
from typing import (
    Any,
    Callable,
    Dict,
    Iterable,
    List,
    NamedTuple,
    Optional,
    Tuple,
    TypeVar,
    cast,
)
from llvmlite.binding import ValueRef, TypeRef

from metalift.analysis_new import VariableTracker
from metalift.synthesize_auto import synthesize as run_synthesis  # type: ignore
from llvmlite import binding as llvm

from metalift.ir import (
    Add,
    Bool,
    Call,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    FnT,
    Gt,
    Implies,
    Int,
    Ite,
    Le,
    ListT,
    Lit,
    Lt,
    Mul,
    Not,
    Object,
    Pointer,
    SetT,
    Sub,
    Synth,
    TupleT,
    Type as MLType,
    Var,
    parseTypeRef,
)

import copy

from metalift.analysis import setupBlocks

from metalift.vc import Block

from metalift.vc_util import and_exprs, or_exprs

# Run the interpreted version of mypy instead of the compiled one to avoid
# TypeError: interpreted classes cannot inherit from compiled traits
# from https://github.com/python/mypy
# python3 -m pip install --no-binary mypy -U mypy

# Helper classes
RawLoopInfo = NamedTuple(
    "LoopInfo",
    [
        ("header_name", List[str]),
        ("body_names", List[str]),
        ("exit_names", List[str]),
        ("latche_names", List[str]),
    ],
)

class LoopInfo:
    header: Block
    body: List[Block]
    exits: List[Block]
    latches: List[Block]
    havocs: List[ValueRef]

    def __init__(
        self,
        header: Block,
        body: List[Block],
        exits: List[Block],
        latches: List[Block],
    ) -> None:
        self.header = header
        self.body = body
        self.exits = exits
        self.latches = latches

        self.havocs: List[ValueRef] = []
        for block in [self.header, *self.body, *self.exits, *self.latches]:
            for i in block.instructions:
                opcode = i.opcode
                ops = list(i.operands)
                # prevent duplicate havocs in nested loops
                # TODO jie: why are havocs only from store instructions
                if opcode == "store" and ops[1] not in self.havocs:
                    self.havocs.append(ops[1])

        # Remove back edges
        for latch in self.latches:
            latch.succs.remove(self.header)
            self.header.preds.remove(latch)

    @staticmethod
    def from_raw_loop_info(raw_loop_info: RawLoopInfo, blocks: Dict[str, Block]) -> "LoopInfo":
        return LoopInfo(
            header=blocks[raw_loop_info.header_name],
            body=[blocks[body_name] for body_name in raw_loop_info.body_names],
            exit=[blocks[exit_name] for exit_name in raw_loop_info.exit_names],
            latch=[blocks[latch_name] for latch_name in raw_loop_info.latch_names],
        )

    @staticmethod
    def from_block_names(
        header_name: str,
        body_names: List[str],
        exit_names: List[str],
        latch_names: List[str],
        blocks: Dict[str, Block]
    ) -> "LoopInfo":
        return LoopInfo(
            header=blocks[header_name],
            body=[blocks[body_name] for body_name in body_names],
            exit=[blocks[exit_name] for exit_name in exit_names],
            latch=[blocks[latch_name] for latch_name in latch_names],
        )


# Helper functions
def parse_loops(loops_filepath: str, fn_name: str) -> List[RawLoopInfo]:
    with open(loops_filepath, mode="r") as f:
        found_lines = []
        found = False
        for l in f.readlines():
            if re.match(
                "Printing analysis 'Natural Loop Information' for function '%s':"
                % fn_name,
                l,
            ):
                found = True
            elif found:
                loop_match = re.match("Loop at depth \d+ containing: (\S+)", l.strip())
                if loop_match:
                    found_lines.append(loop_match.group(1))
                elif re.match(
                    "Printing analysis 'Natural Loop Information' for function '\S+':",
                    l,
                ):
                    found = False

        loops: List[LoopInfo] = []
        for m in found_lines:
            header_names: List[str] = []
            body_names: List[str] = []
            exit_names: List[str] = []
            latch_names: List[str] = []

            blks = m.replace("%", "").split(",")
            for b in blks:
                name: str = re.search("([^<]+)", b).group(0)  # type: ignore
                print("name: %s" % b)
                if "<header>" in b:
                    header_names.append(name)
                if "<exiting>" in b:
                    exit_names.append(name)
                if "<latch>" in b:
                    latch_names.append(name)
                if "<header>" not in b and "<exiting>" not in b and "latch" not in b:
                    body_names.append(name)
            if len(header_names) > 1:
                raise Exception(f"Detected more than one header block! {header_names}")

            raw_loop_info = RawLoopInfo(
                header_name=header_names[0],
                body_names=body_names,
                exit_names=exit_names,
                latch_names=latch_names
            )
            loops.append(raw_loop_info)

        for loop in loops:
            print(
                "found loop: header: %s, body: %s, exits: %s, latches: %s"
                % (loop.header, loop.body, loop.exits, loop.latches)
            )
        return loops

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
    grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr]
    synth: Optional[Synth]

    # argument ordering convention:
    # original arguments of the fn first in its original order, then vars that are in scope
    # and not one of the original arguments in sorted order
    def __init__(
        self,
        args: List[LLVMVar],
        writes: List[LLVMVar],
        reads: List[LLVMVar],
        in_scope: List[LLVMVar],
        name: str,
        grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
    ) -> None:
        self.args = args
        self.writes = writes
        self.reads = reads
        self.in_scope = in_scope
        self.name = name
        self.grammar = grammar
        self.synth = None

    def call(self, state: State) -> Call:
        return Call(self.name, Bool(), *[state.read(v[0]) for v in self.args])

    def gen_Synth(self) -> Synth:
        # print(f"gen args: {self.args}, writes: {self.writes}, reads: {self.reads}, scope: {self.in_scope}")
        writes = [Var(v[0], v[1]) for v in self.writes]
        reads = [Var(v[0], v[1]) for v in self.reads]
        in_scope = [Var(v[0], v[1]) for v in self.in_scope]

        v_exprs = [self.grammar(v, writes, reads, in_scope) for v in writes]

        body = and_exprs(*v_exprs)

        vars = [Var(v[0], v[1]) for v in self.args]
        return Synth(self.name, body, *vars)


class PredicateTracker:
    types: Dict[ValueRef, TypeRef]
    predicates: Dict[int, Predicate]

    def __init__(self) -> None:
        self.types = dict()
        self.predicates = dict()

    def invariant(
        self,
        fn_name: str,
        inv_num: int,
        args: List[LLVMVar],
        writes: List[LLVMVar],
        reads: List[LLVMVar],
        in_scope: List[LLVMVar],
        grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
    ) -> Predicate:
        if inv_num in self.predicates.keys():
            return self.predicates[inv_num]
        else:
            non_args_scope_vars = list(set(in_scope) - set(args))
            non_args_scope_vars.sort()
            args = (
                args + non_args_scope_vars
            )  # add the vars that are in scope but not part of args, in sorted order

            inv = Predicate(
                args=args,
                writes=writes,
                reads=reads,
                in_scope=in_scope,
                name=f"{fn_name}_inv{inv_num}",
                grammar=grammar
            )
            self.predicates[inv_num] = inv
            return inv

    def postcondition(
        self,
        o: ValueRef,
        outs: List[LLVMVar],
        ins: List[LLVMVar],
        grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
    ) -> Predicate:
        if o in self.predicates:
            return self.predicates[o]
        else:
            ps = Predicate(ins + outs, outs, ins, [], f"{o.name}_ps", grammar)
            self.predicates[o] = ps
            return ps

    def call(self, o: ValueRef, s: State) -> Call:
        return self.predicates[o].call(s)


class VCVisitor:
    fn_name: str
    fn_type: MLType
    fn_ref: ValueRef
    fn_args: List[Expr]
    formals: List[LLVMVar] # TODO jie: refactor this by using fn_args
    fn_blocks: Dict[str, Block]
    fn_blocks_states: Dict[str, State]

    var_tracker: VariableTracker
    pred_tracker: PredicateTracker

    inv_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr]
    ps_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr]

    loops: List[LoopInfo]

    def __init__(
        self,
        fn_name: str,
        fn_type: MLType,
        fn_ref: ValueRef,
        fn_args: List[Expr],
        fn_blocks: Dict[str, Block],
        var_tracker: VariableTracker,
        pred_tracker: PredicateTracker,
        inv_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
        loops: List[LoopInfo]
    ) -> None:
        self.fn_name = fn_name
        self.fn_type = fn_type
        self.fn_ref = fn_ref
        self.fn_args = fn_args
        self.fn_blocks = fn_blocks
        self.fn_blocks_states: Dict[str, State] = defaultdict(lambda: State())

        self.var_tracker = var_tracker
        self.pred_tracker = pred_tracker

        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar

        self.loops = loops

    # Helper functions
    def write_to_block(self, block_name: str, var: str, val: Expr) -> None:
        self.fn_blocks_states[block_name].vars[var] = val

    def read_from_block(self, block_name: str, ref: ValueRef) -> Expr:
        blk_state_vars = self.fn_blocks_states[block_name].vars
        if ref.name:
            if ref.name in blk_state_vars.keys():
                return blk_state_vars[ref.name]
            else:
                raise Exception(f"{ref.name} not found in {blk_state_vars}")
        else:
            val = re.search("\w+ (\S+)", str(ref)).group(1)  # type: ignore
            if val == "true":
                return Lit(True, Bool())
            elif val == "false":
                return Lit(False, Bool())
            else:  # assuming it's a number
                return Lit(int(val), Int())

    def find_header_loops(self, block_name: str) -> List[LoopInfo]:
        # TODO: an a block be the header of two loops
        relevant_loops: List[LoopInfo] = []
        for loop in self.loops:
            if block_name == loop.header.name:
                relevant_loops.append(loop)
        return relevant_loops

    def find_header_pred_loops(self, block_name: str) -> List[LoopInfo]:
        # TODO: an a block be the header preprocessor of two loops
        relevant_loops: List[LoopInfo] = []
        for loop in self.loops:
            header_preds = loop.header.preds
            if any([block_name == pred.name for pred in header_preds]):
                relevant_loops.append(loop)
        return relevant_loops

    def find_latch_loops(self, block_name: str) -> List[LoopInfo]:
        # TODO: an a block be the header preprocessor of two loops
        relevant_loops: List[LoopInfo] = []
        for loop in self.loops:
            if any([block_name == latch.name for latch in loop.latches]):
                relevant_loops.append(loop)
        return relevant_loops

    # Definitions
    def preprocess(self, block: ValueRef) -> None:
        ret_type: MLType = self.fn_type.args[0]
        arg_types: List[MLType] = self.fn_type.args[1]
        arg_names: List[str] = [a.name() for a in self.fn_args]
        self.formals = list(zip(arg_names, arg_types))
        self.pred_tracker.postcondition(
            self.fn_ref,
            [(f"{self.fn_name}_rv", ret_type)],
            self.formals,
            self.ps_grammar,
        )
        for arg in self.fn_args:
            self.write_to_block(block.name, arg.name(), arg)

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
            raise Exception(f"Unsupported instruction opcode {o.opcode}")

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
            var_state: Dict[str, Dict[Expr, List[Expr]]] = defaultdict(
                lambda: defaultdict(list)
            )
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
                        value_to_aggregated_precond[value] = or_exprs(
                            *all_aggregated_preconds
                        )

                    merged_value = None
                    for (
                        value,
                        aggregated_precond,
                    ) in value_to_aggregated_precond.items():
                        if merged_value is None:
                            merged_value = value
                        else:
                            merged_value = Ite(aggregated_precond, value, merged_value)
                    merged_vars[var_name] = merged_value
            blk_state.vars = merged_vars
            # TODO: how to handle asserts here?

    def visit_llvm_block(self, block: ValueRef) -> None:
        # If this block is the header of a loop, havoc the modified vars
        header_loops = self.find_header_loops(block.name)
        if len(header_loops) > 0:
            for loop in header_loops:
                havocs: List[LLVMVar] = []
                for var in loop.havocs:
                    var_name, var_type = var.name, parseTypeRef(var.type)
                    havocs.append(LLVMVar(var_name, var_type))
                    new_value = self.var_tracker.variable(var_name, var_type)
                    self.write_to_block(var_name, new_value)
                loop_index = self.loops.index(loop)
                inv = self.pred_tracker.invariant(
                    fn_name=self.fn_name,
                    args=self.formals,
                    writes=havocs,
                    reads=[], # TODO
                    in_scope=[], # TODO
                    grammar=self.inv_grammar
                )

        # Visit the block
        if len(block.preds) == 0:
            self.preprocess(block)
        else:
            # First we need to merge states
            self.merge_states(block)
        self.visit_instructions(block.name, block.instructions)
        self.fn_blocks_states[block.name].processed = True

        # If this block is the latch of some loops, assert inv is true
        latch_loops = self.find_latch_loops(block.name)
        if len(latch_loops) > 0:
            self.fn_blocks_states[block.name].asserts.append()

    def visit_instructions(self, block_name: str, instructions: List[ValueRef]) -> None:
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
        self.write_to_block(block_name, o.name, Pointer(val))

    def visit_load_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        ptr_expr = self.read_from_block(block_name, ops[0])
        is_ptr_expr = isinstance(ptr_expr, Pointer)
        is_ite_expr_with_ptr = (
            isinstance(ptr_expr, Ite)
            and isinstance(ptr_expr.e1(), Pointer)
            and isinstance(ptr_expr.e2(), Pointer)
        )
        if is_ptr_expr:
            referenced_value = ptr_expr.value
        elif is_ite_expr_with_ptr:
            referenced_value = Ite(
                ptr_expr.c(), ptr_expr.e1().value, ptr_expr.e2().value
            )
        else:
            raise Exception

        self.write_to_block(block_name, o.name, referenced_value)

    def visit_store_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        value_to_store = self.read_from_block(block_name, ops[0])
        # store into the location stored in ops[1].name
        ptr_expr = self.read_from_block(block_name, ops[1])
        if not isinstance(ptr_expr, Pointer):
            raise Exception(f"Store instruction {o} must store into a pointer!")
        cast(Pointer, ptr_expr).set_value(value_to_store)

    def visit_add_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        add_expr = Add(
            self.read_from_block(block_name, ops[0]),
            self.read_from_block(block_name, ops[1]),
        )
        self.write_to_block(block_name, o.name, add_expr)

    def visit_sub_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        sub_expr = Sub(
            self.read_from_block(block_name, ops[0]),
            self.read_from_block(block_name, ops[1]),
        )
        self.write_to_block(block_name, o.name, sub_expr)

    def visit_mul_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        mul_expr = Mul(
            self.read_from_block(block_name, ops[0]),
            self.read_from_block(block_name, ops[1]),
        )
        self.write_to_block(block_name, o.name, mul_expr)

    def visit_icmp_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        cond = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(o).strip()).group(1)
        op0 = self.read_from_block(block_name, ops[0])
        op1 = self.read_from_block(block_name, ops[1])

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

        self.write_to_block(block_name, o.name, value)

    def visit_br_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        if len(ops) > 1:
            # LLVMLite switches the order of branches for some reason
            true_branch = ops[2].name
            false_branch = ops[1].name
            cond = self.read_from_block(block_name, ops[0])
            self.fn_blocks_states[true_branch].precond.append(cond)
            self.fn_blocks_states[false_branch].precond.append(Not(cond))

    def visit_ret_instruction(self, block_name: str, o: ValueRef) -> None:
        # TODO: hanlde ret void
        blk_state = self.fn_blocks_states[block_name]
        ops = list(o.operands)
        ps = Call(
            self.pred_tracker.predicates[self.fn_ref].name,
            Bool(),
            *self.fn_args,
            self.read_from_block(block_name, ops[0]),
        )
        if blk_state.precond:
            blk_state.asserts.append(Implies(and_exprs(*blk_state.precond), ps))
        else:
            blk_state.asserts.append(ps)
        print(f"ps: {blk_state.asserts[-1]}")
        blk_state.has_returned = True


class Driver:
    var_tracker: VariableTracker
    pred_tracker: PredicateTracker
    asserts: List[Expr]
    postconditions: List[Expr]
    fns: Dict[str, "MetaliftFunc"]  # maps analyzed function names to returned object
    target_fn: Callable[[], List[FnDecl]]

    def __init__(self) -> None:
        self.var_tracker = VariableTracker()
        self.pred_tracker = PredicateTracker()
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
        inv_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
    ) -> "MetaliftFunc":
        f = MetaliftFunc(
            driver=self,
            llvm_filepath=llvm_filepath,
            loops_filepath=loops_filepath,
            fn_name=fn_name,
            target_lang_fn=target_lang_fn,
            inv_grammar=inv_grammar,
            ps_grammar=ps_grammar,
        )
        self.fns[fn_name] = f
        return f

    def synthesize(self) -> None:
        synths = [i.gen_Synth() for i in self.pred_tracker.predicates.values()]

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
    fn_name: str
    fn_type: MLType
    fn_ref: ValueRef  # TODO jie: should I change this to llvm_ir.Function
    fn_blocks: Dict[str, Block]

    target_lang_fn: Callable[[], List[FnDecl]]
    inv_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr]
    ps_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr]
    synthesized: Optional[Expr]

    loops: List[LoopInfo]


    def __init__(
        self,
        driver: Driver,
        llvm_filepath: str,
        loops_filepath: str,
        fn_name: str,
        target_lang_fn: Callable[[], List[FnDecl]],
        inv_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
        ps_grammar: Callable[[Var, List[Var], List[Var], List[Var]], Expr],
    ) -> None:
        self.driver = driver

        self.fn_name = fn_name
        with open(llvm_filepath, mode="r") as file:
            ref = llvm.parse_assembly(file.read())
        self.fn_ref = ref.get_function(fn_name)
        # Find the return type of function, and set self.fn_type
        return_type = find_return_type(self.fn_blocks.values())
        fn_args_types = [parseTypeRef(a.type) for a in self.fn_ref.arguments]
        self.fn_type = FnT(return_type, fn_args_types)
        self.fn_blocks = setupBlocks(self.fn_ref.blocks)

        self.target_lang_fn = target_lang_fn
        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar
        self.synthesized = None

        # Parse and process loops
        raw_loops: List[RawLoopInfo] = parse_loops(loops_filepath, fn_name)
        self.loops = [LoopInfo.from_raw_loop_info(raw_loop) for raw_loop in raw_loops]

    def __call__(self, *args: Any, **kwds: Any) -> Any:
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
                raise Exception(
                    f"Expecting the {i}th argument to have name {fn_arg_name} but instead got {passed_in_arg_name}"
                )
            if passed_in_arg_type != fn_arg_type:
                raise RuntimeError(
                    f"expect {fn_arg_name} to have type {fn_arg_type} rather than {passed_in_arg_name}"
                )

        v = VCVisitor(
            fn_name=self.fn_name,
            fn_type=self.fn_type,
            fn_ref=self.fn_ref,
            fn_args=list(args),
            fn_blocks=self.fn_blocks,
            var_tracker=self.driver.var_tracker,
            pred_tracker=self.driver.pred_tracker,
            inv_grammar=self.inv_grammar,
            ps_grammar=self.ps_grammar,
            loops=self.loops
        )
        done = False
        while not done:
            done = True
            for b in self.fn_blocks.values():
                if not v.fn_blocks_states[b.name].processed and (
                    not b.preds
                    or all([v.fn_blocks_states[p.name].processed for p in b.preds])
                ):
                    v.visit_llvm_block(b)
                    done = False

        ret_val = self.driver.var_tracker.variable(
            f"{self.fn_name}_rv", self.fn_type.args[0]
        )

        ps = Call(f"{self.fn_name}_ps", Bool(), ret_val, *args)

        self.driver.postconditions.append(ps)

        for block in self.fn_blocks.values():
            self.driver.asserts.extend(v.fn_blocks_states[block.name].asserts)

        return ret_val

    T = TypeVar("T")

    def codegen(self, codegen_fn: Callable[[Expr], T]) -> T:
        if self.synthesized is None:
            raise Exception(f"{self.fn_name} is not synthesized yet")
        else:
            return codegen_fn(self.synthesized)

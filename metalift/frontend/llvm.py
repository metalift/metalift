import copy
import re
import subprocess
from collections import defaultdict
from typing import (
    Any,
    Callable,
    Dict,
    Iterable,
    List,
    NamedTuple,
    Optional,
    Set,
    Tuple,
    TypeVar,
    cast,
)
import typing

from llvmlite import binding as llvm
from llvmlite.binding import TypeRef, ValueRef

from metalift import models
from metalift.analysis import setupBlocks
from metalift.analysis_new import VariableTracker
from metalift.frontend.utils import ExprDict
from metalift.ir import (
    Add,
    And,
    BoolObject,
    Call,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    FnT,
    Gt,
    Implies,
    IntObject,
    Ite,
    Le,
    Lit,
    Lt,
    Mul,
    NewObject,
    Not,
    ObjectExpr,
    Or,
    Pointer,
    SetObject,
    Sub,
    Synth,
    TupleT,
    ListObject,
    call,
    create_object,
    get_object_exprs,
    implies,
    parse_type_ref_to_obj,
    Var,
)
from metalift.ir_util import MLType, is_object_pointer_type

from metalift.synthesize_auto import synthesize as run_synthesis  # type: ignore
from metalift.vc import Block
from metalift.vc_util import and_exprs, and_objects, or_exprs, or_objects

# Helper classes
RawLoopInfo = NamedTuple(
    "RawLoopInfo",
    [
        ("header_name", str),
        ("body_names", List[str]),
        ("exit_names", List[str]),
        ("latch_names", List[str]),
    ],
)


class LoopInfo:
    header: Block
    body: List[Block]
    exits: List[Block]
    latches: List[Block]
    # We use a lists instead of a set here to make sure they are always sorted
    # havocs that are vectors, need to be written to `primitive_vars`
    vector_havocs: List[ValueRef]
    # Other havocs, need to be written to `pointer_vars`
    non_vector_havocs: List[ValueRef]

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

        self.vector_havocs: List[ValueRef] = []
        self.non_vector_havocs: List[ValueRef] = []
        for block in [self.header, *self.body, *self.exits, *self.latches]:
            for i in block.instructions:
                opcode = i.opcode
                ops = list(i.operands)
                if opcode == "store" and ops[1] not in self.non_vector_havocs:
                    self.non_vector_havocs.append(ops[1])
                elif opcode == "call":
                    args = ops[:-1]
                    fn_name = get_fn_name_from_call_instruction(i)
                    if fn_name == "push_back":
                        self.vector_havocs.append(args[0])

        # Remove back edges
        for latch in self.latches:
            latch.succs.remove(self.header)
            self.header.preds.remove(latch)

    @staticmethod
    def from_raw_loop_info(
        raw_loop_info: RawLoopInfo, blocks: Dict[str, Block]
    ) -> "LoopInfo":
        return LoopInfo(
            header=blocks[raw_loop_info.header_name],
            body=[blocks[body_name] for body_name in raw_loop_info.body_names],
            exits=[blocks[exit_name] for exit_name in raw_loop_info.exit_names],
            latches=[blocks[latch_name] for latch_name in raw_loop_info.latch_names],
        )


def get_fn_name_from_call_instruction(o: ValueRef) -> str:
    ops = list(o.operands)
    raw_fn_name: str = ops[-1] if isinstance(ops[-1], str) else ops[-1].name
    if raw_fn_name == "":
        # TODO(shadaj): this is a hack around LLVM bitcasting the function before calling it on aarch64
        fn_name = str(ops[-1]).split("@")[-1].split(" ")[0]
    else:
        demangled_name = get_demangled_name(raw_fn_name)
        if demangled_name is None:
            raise Exception(f"Could not demangle function name {raw_fn_name}")
        fn_name = demangled_name
    return fn_name


def parse_loops(loops_filepath: str, raw_fn_name: str) -> List[RawLoopInfo]:
    # raw_fn_name may be mangled
    with open(loops_filepath, mode="r") as f:
        found_lines = []
        found = False
        for l in f.readlines():
            if re.match(
                "Printing analysis 'Natural Loop Information' for function '%s':"
                % raw_fn_name,
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

        raw_loops: List[RawLoopInfo] = []
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
                latch_names=latch_names,
            )
            raw_loops.append(raw_loop_info)

        for loop in raw_loops:
            print(
                "found loop: header: %s, body: %s, exits: %s, latches: %s"
                % (loop.header_name, loop.body_names, loop.exit_names, loop.latch_names)
            )
        return raw_loops


def is_sret_arg(arg: ValueRef) -> bool:
    return b"sret" in arg.attributes


def find_return_type_and_sret_arg(
    fn_ref: ValueRef, blocks: Iterable[ValueRef]
) -> Tuple[typing.Type[NewObject], ValueRef]:
    # First check if there are sret arguments. Currently, we only support at most one sret argument.
    sret_arg: Optional[ValueRef] = None
    for arg in fn_ref.arguments:
        if is_sret_arg(arg):
            if sret_arg is None:
                sret_arg = arg
            else:
                raise Exception("multiple sret arguments: %s and %s" % (sret_arg, arg))
    if sret_arg is not None:
        return parse_type_ref_to_obj(sret_arg.type), sret_arg

    # If there are no sret args, we try to find the return type by parsing the ret instructions
    return_type = None
    for block in blocks:
        final_instruction = block.instructions[-1]
        if final_instruction.opcode == "ret":
            ops = list(final_instruction.operands)
            curr_return_type = parse_type_ref_to_obj(ops[0].type)
            if return_type is not None and return_type != curr_return_type:
                raise Exception("Return types are not consistent across blocks!")
            return_type = curr_return_type
    if return_type is None:
        raise RuntimeError(f"fn must return a value!")
    return return_type, None


def parse_object_func(blocksMap: Dict[str, Block]) -> None:
    p = re.compile("ML_(\w+)_(set|get)_(\w+)")
    for b in blocksMap.values():
        for i in b.instructions:
            opcode = i.opcode
            ops = list(i.operands)

            if opcode == "call":
                fnName = ops[-1].name
                r = p.search(fnName)
                if r:
                    className = r.group(1)  # not used
                    op = r.group(2)
                    fieldName = r.group(3)
                    if op == "set":
                        # newInst = MLInst_Call("setField", i.type, Lit(fieldName, String()), ops[0], ops[1])
                        setattr(
                            i,
                            "my_operands",
                            [
                                Lit(fieldName, String()),
                                ops[0],
                                ops[1],
                                "setField",
                            ],
                        )
                    else:
                        # i.operands = ["getField", i.type, Lit(fieldName, String()), ops[0], "getField"]
                        setattr(
                            i,
                            "my_operands",
                            [Lit(fieldName, String()), ops[0], "getField"],
                        )
                        # print("inst: %s" % i)


def get_demangled_name(maybe_mangled_name: str) -> Optional[str]:
    # Note: this function does not raise exception, it's up to the caller to raise exceptions if the name cannot be demangled
    result = subprocess.run(
        ["c++filt", "-n", maybe_mangled_name], stdout=subprocess.PIPE, check=True
    )
    stdout = result.stdout.decode("utf-8").strip()
    match = re.match(
        f"^(.* )?(.*::)*(~?[a-zA-Z0-9_]+(\[\])?)(<.*>)?\(.*\)( const)?$", stdout
    )
    if match is not None:
        return match.group(3)

    match = re.match(f"^([a-zA-Z0-9_]+)(\(.*\))?$", stdout)
    if match is not None:
        return match.group(1)

    return None


LLVMVar = NamedTuple(
    "LLVMVar",
    [
        ("var_name", str),
        ("var_type", typing.Type[NewObject]),
    ],
)


class State:
    precond: List[BoolObject]
    primitive_vars: Dict[str, NewObject]
    pointer_vars: Dict[str, NewObject]
    asserts: List[BoolObject]
    has_returned: bool
    processed: bool

    def __init__(
        self,
        precond: Optional[List[BoolObject]] = None,
        primitive_vars: Optional[Dict[str, NewObject]] = None,
        pointer_vars: Optional[Dict[str, NewObject]] = None,
        asserts: Optional[List[BoolObject]] = None,
        has_returned: bool = False,
    ) -> None:
        self.precond = precond or []
        self.primitive_vars = primitive_vars or {}
        self.pointer_vars = pointer_vars or {}
        self.asserts = asserts or []
        self.has_returned = has_returned if not has_returned else has_returned
        self.processed = False

    def read_operand(self, op: ValueRef) -> NewObject:
        if op.name:
            return self.read_var(op.name)
        val = re.search("\w+ (\S+)", str(op)).group(1)  # type: ignore
        if val == "true":
            return BoolObject(True)
        elif val == "false":
            return BoolObject(False)
        else:  # assuming it's a number
            return IntObject(int(val))

    def load_operand(self, op: ValueRef) -> NewObject:
        if not op.name:
            raise Exception(f"Cannot load value from an operand without name")
        if op.name in self.pointer_vars.keys():
            return self.pointer_vars[op.name]
        raise RuntimeError(f"{op.name} not found in pointer vars {self.pointer_vars}")

    def write_operand(self, op: ValueRef, value: NewObject) -> None:
        if not op.name:
            raise Exception("Cannot write value for an operand without name")
        self.primitive_vars[op.name] = value

    def store_operand(self, op: ValueRef, value: NewObject) -> None:
        if not op.name:
            raise Exception("Cannot store value into an operand without name")
        self.pointer_vars[op.name] = value

    def read_var(self, var_name: str) -> NewObject:
        if var_name in self.primitive_vars.keys():
            return self.primitive_vars[var_name]
        raise RuntimeError(
            f"{var_name} not found in primitive vars {self.primitive_vars}"
        )

    def load_var(self, var_name: str) -> NewObject:
        if var_name in self.pointer_vars.keys():
            return self.pointer_vars[var_name]
        raise RuntimeError(
            f"{var_name} not found in primitive vars {self.pointer_vars}"
        )

    def write_var(self, var_name: str, value: NewObject) -> None:
        self.primitive_vars[var_name] = value

    def store_var(self, var_name: str, value: NewObject) -> None:
        self.pointer_vars[var_name] = value

    def read_or_load_var(self, var_name: str) -> NewObject:
        if var_name in self.primitive_vars.keys():
            return self.primitive_vars[var_name]
        if var_name in self.pointer_vars.keys():
            return self.pointer_vars[var_name]
        raise RuntimeError(
            f"{var_name} not found in primitive vars {self.primitive_vars} and pointer vars {self.pointer_vars}"
        )


class Predicate:
    driver: "Driver"
    args: List[NewObject]
    writes: List[NewObject]
    reads: List[NewObject]
    name: str
    grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    synth: Optional[Synth]

    # argument ordering convention:
    # original arguments of the fn first in its original order, then vars that are in scope
    # and not one of the original arguments in sorted order
    def __init__(
        self,
        driver: "Driver",
        args: List[NewObject],
        writes: List[NewObject],
        reads: List[NewObject],
        name: str,
        grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
    ) -> None:
        self.driver = driver
        self.args = args
        self.writes = writes
        self.reads = reads
        self.name = name
        self.grammar = grammar
        self.synth = None

    def call(self, state: State) -> BoolObject:
        call_expr = Call(
            self.name,
            BoolObject,
            *[state.read_or_load_var(v.var_name()) for v in self.args],
        )
        return BoolObject(call_expr)

    def gen_Synth(self) -> Synth:
        v_objects = [self.grammar(v, self.writes, self.reads) for v in self.writes]
        [print(f"v: {v}\n") for v in v_objects]
        body = and_exprs(*get_object_exprs(v_objects))
        return Synth(self.name, body, *self.args)


class PredicateTracker:
    driver: "Driver"
    types: Dict[ValueRef, TypeRef]
    predicates: Dict[str, Predicate]

    def __init__(self, driver: "Driver") -> None:
        self.driver = driver
        self.types = dict()
        self.predicates = dict()

    def invariant(
        self,
        inv_name: str,
        args: List[NewObject],
        writes: List[NewObject],
        reads: List[NewObject],
        grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
    ) -> Predicate:
        if inv_name in self.predicates.keys():
            return self.predicates[inv_name]
        else:
            inv = Predicate(
                driver=self.driver,
                args=args,
                writes=writes,
                reads=reads,
                name=inv_name,
                grammar=grammar,
            )
            self.predicates[inv_name] = inv
            return inv

    def postcondition(
        self,
        fn_name: str,
        outs: List[NewObject],
        ins: List[NewObject],
        grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
    ) -> Predicate:
        if fn_name in self.predicates:
            return self.predicates[fn_name]
        else:
            ps = Predicate(self.driver, ins + outs, outs, ins, f"{fn_name}_ps", grammar)
            self.predicates[fn_name] = ps
            return ps

    def VCall(self, name: str, s: State) -> Call:
        return self.predicates[name].call(s)


class VCVisitor:
    driver: "Driver"
    fn_name: str
    fn_type: MLType
    fn_args: List[NewObject]  # whose src are variables
    fn_sret_arg: Optional[NewObject]
    fn_blocks_states: Dict[str, State]

    var_tracker: VariableTracker
    pred_tracker: PredicateTracker

    inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]

    loops: List[LoopInfo]

    def __init__(
        self,
        driver: "Driver",
        fn_name: str,
        fn_type: MLType,
        fn_args: List[NewObject],
        fn_sret_arg: Optional[NewObject],
        var_tracker: VariableTracker,
        pred_tracker: PredicateTracker,
        inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        loops: List[LoopInfo],
    ) -> None:
        self.driver = driver
        self.fn_name = fn_name
        self.fn_type = fn_type
        self.fn_args = fn_args
        self.fn_sret_arg = fn_sret_arg
        self.fn_blocks_states: Dict[str, State] = defaultdict(lambda: State())

        self.var_tracker = var_tracker
        self.pred_tracker = pred_tracker

        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar

        self.loops = loops

    # Helper functions
    # Helper functions for reading and writing variables
    def read_operand_from_block(
        self, block_name: str, op: ValueRef
    ) -> NewObject:  # Primitive
        blk_state = self.fn_blocks_states[block_name]
        return blk_state.read_operand(op)

    def load_operand_from_block(
        self, block_name: str, op: ValueRef
    ) -> NewObject:  # Pointer
        blk_state = self.fn_blocks_states[block_name]
        return blk_state.load_operand(op)

    def write_operand_to_block(
        self, block_name: str, op: ValueRef, val: NewObject
    ) -> None:  # Primitive
        blk_state = self.fn_blocks_states[block_name]
        return blk_state.write_operand(op, val)

    def store_operand_to_block(
        self, block_name: str, op: ValueRef, val: NewObject
    ) -> None:  # Pointer
        blk_state = self.fn_blocks_states[block_name]
        return blk_state.store_operand(op, val)

    def double_store_operand_to_block(
        self, block_name: str, op: ValueRef, val: NewObject
    ) -> None:
        blk_state = self.fn_blocks_states[block_name]
        return blk_state.store_operand(op, val)

    def write_var_to_block(
        self, block_name: str, var_name: str, val: NewObject
    ) -> None:
        blk_state = self.fn_blocks_states[block_name]
        return blk_state.write_var(var_name, val)

    def store_var_to_block(
        self, block_name: str, var_name: str, val: NewObject
    ) -> None:
        blk_state = self.fn_blocks_states[block_name]
        return blk_state.store_var(var_name, val)

    # Helper functions for loops
    def find_header_loops(self, block_name: str) -> List[LoopInfo]:
        relevant_loops: List[LoopInfo] = []
        for loop in self.loops:
            if block_name == loop.header.name:
                relevant_loops.append(loop)
        return relevant_loops

    def find_header_pred_loops(self, block_name: str) -> List[LoopInfo]:
        relevant_loops: List[LoopInfo] = []
        for loop in self.loops:
            header_preds = loop.header.preds
            if any([block_name == pred.name for pred in header_preds]):
                relevant_loops.append(loop)
        return relevant_loops

    def find_latch_loops(self, block_name: str) -> List[LoopInfo]:
        relevant_loops: List[LoopInfo] = []
        for loop in self.loops:
            if any([block_name == latch.name for latch in loop.latches]):
                relevant_loops.append(loop)
        return relevant_loops

    def get_vector_havocs(self, loop_info: LoopInfo) -> List[NewObject]:
        res = []
        for var in loop_info.vector_havocs:
            parsed_type = parse_type_ref_to_obj(var.type)
            # TODO colin: add generic (ie containedT) support needed for objects and different types of objects
            res.append(create_object(parsed_type, var.name))
        return res

    def get_non_vector_havocs(self, loop_info: LoopInfo) -> List[NewObject]:
        res = []
        for var in loop_info.non_vector_havocs:
            parsed_type = parse_type_ref_to_obj(var.type)
            res.append(create_object(parsed_type, var.name))
        return res

    # Functions to step through the blocks
    def preprocess(self, block: ValueRef) -> None:
        """Preprocess the entry block of the entire function. This includes setting up the postcondition, as well as writing all the arguments to the state of the entry block."""
        return_arg = create_object(self.fn_type.args[0], f"{self.fn_name}_rv")
        for arg in self.fn_args + [return_arg]:
            # TODO: make this check for all pointer types
            if is_object_pointer_type(arg):
                self.store_var_to_block(block.name, arg.var_name(), arg)
            else:
                self.write_var_to_block(block.name, arg.var_name(), arg)

        if self.fn_sret_arg is not None:
            if is_object_pointer_type(self.fn_sret_arg):
                self.store_var_to_block(
                    block.name, self.fn_sret_arg.var_name(), self.fn_sret_arg
                )
            else:
                self.write_var_to_block(
                    block.name, self.fn_sret_arg.var_name(), self.fn_sret_arg
                )
        self.pred_tracker.postcondition(
            self.fn_name,
            [return_arg],  # TODO: I feel like this flow could be better
            self.fn_args,
            self.ps_grammar,
        )

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
        elif o.opcode == "bitcast":
            self.visit_bitcast_instruction(block_name, o)
        elif o.opcode == "sext":
            self.visit_sext_instruction(block_name, o)
        elif o.opcode == "icmp":
            self.visit_icmp_instruction(block_name, o)
        elif o.opcode == "br":
            self.visit_br_instruction(block_name, o)
        elif o.opcode == "ret":
            self.visit_ret_instruction(block_name, o)
        elif o.opcode == "call":
            self.visit_call_instruction(block_name, o)
        else:
            raise Exception(f"Unsupported instruction opcode {o.opcode}")

    def merge_states(self, block: ValueRef) -> None:
        blk_state = self.fn_blocks_states[block.name]

        if len(block.preds) == 0:
            return
        elif len(block.preds) == 1:
            pred_state = self.fn_blocks_states[block.preds[0].name]
            blk_state.primitive_vars = copy.deepcopy(pred_state.primitive_vars)
            blk_state.pointer_vars = copy.deepcopy(pred_state.pointer_vars)
            blk_state.precond.extend(copy.deepcopy(pred_state.precond))
            blk_state.has_returned = False
            blk_state.processed = False
        else:
            pred_preconds: List[BoolObject] = []
            for pred in block.preds:
                pred_state = self.fn_blocks_states[pred.name]
                if len(pred_state.precond) > 1:
                    pred_preconds.append(and_objects(*pred_state.precond))
                else:
                    pred_preconds.append(pred_state.precond[0])
            if len(pred_preconds) > 1:
                blk_state.precond = [or_objects(*pred_preconds)]
            else:
                blk_state.precond = pred_preconds

            # TODO(jie): handle global vars and uninterpreted functions

            # Merge primitive and pointer variables
            # Mapping from variable names to a mapping from values to assume statements
            # Merge primitive vars
            primitive_var_state: Dict[
                str, Dict[Expr, List[List[BoolObject]]]
            ] = defaultdict(lambda: defaultdict(list))
            pointer_var_state: Dict[
                str, Dict[Expr, List[List[BoolObject]]]
            ] = defaultdict(lambda: defaultdict(list))
            for pred in block.preds:
                pred_state = self.fn_blocks_states[pred.name]
                for var_name, var_object in pred_state.primitive_vars.items():
                    var_value_dict = primitive_var_state[var_name]
                    var_expr = var_object.src
                    if var_expr not in var_value_dict:
                        primitive_var_state[var_name][var_expr] = []
                    primitive_var_state[var_name][var_expr].append(pred_state.precond)
                for var_name, var_object in pred_state.pointer_vars.items():
                    var_value_dict = pointer_var_state[var_name]
                    var_expr = var_object.src
                    if var_expr not in var_value_dict:
                        pointer_var_state[var_name][var_expr] = []
                    pointer_var_state[var_name][var_expr].append(pred_state.precond)

            for field_name, var_state in [
                ("primitive_vars", primitive_var_state),
                ("pointer_vars", pointer_var_state),
            ]:
                merged_vars: Dict[str, NewObject] = {}
                for var_name, expr_value_to_precond_mapping in var_state.items():
                    if len(expr_value_to_precond_mapping) == 1:
                        # If there is just one possible value for this variable, we keep this value.
                        merged_expr = list(expr_value_to_precond_mapping.keys())[0]
                    else:
                        # Otherwise if there are multiple possible values for this variable, we create a mapping from possible values to their associated preconditions.
                        expr_value_to_aggregated_precond: Dict[Expr, BoolObject] = {}
                        for (
                            expr_value,
                            all_preconds,
                        ) in expr_value_to_precond_mapping.items():
                            all_aggregated_preconds: List[Expr] = []
                            for preconds in all_preconds:
                                all_aggregated_preconds.append(and_objects(*preconds))
                            expr_value_to_aggregated_precond[expr_value] = or_objects(
                                *all_aggregated_preconds
                            )
                        # Merge the different possible values with an Ite statement.
                        merged_expr: Optional[Expr] = None
                        for (
                            expr_value,
                            aggregated_precond,
                        ) in expr_value_to_aggregated_precond.items():
                            if merged_expr is None:
                                merged_expr = expr_value
                            else:
                                merged_expr = Ite(
                                    aggregated_precond.src, expr_value, merged_expr
                                )
                        if merged_expr is None:
                            # This in theory should never happen, but let's just be safe
                            raise Exception(f"Variable {var_name} has no merged value")
                    merged_object = create_object(merged_expr.type, merged_expr)
                    merged_vars[var_name] = merged_object
                setattr(blk_state, field_name, merged_vars)

    def visit_llvm_block(self, block: ValueRef) -> None:
        # First we need to preprocess the entry block or merge states for non-entry blocks
        if len(block.preds) == 0:
            self.preprocess(block)
        else:
            self.merge_states(block)

        blk_state = self.fn_blocks_states[block.name]
        # If this block is the header of a loop, havoc the modified vars and assume inv
        header_loops = self.find_header_loops(block.name)
        for loop in header_loops:
            vector_havocs = self.get_vector_havocs(loop)
            self.driver.add_var_objects(vector_havocs)
            for vector_havoc in vector_havocs:
                self.write_var_to_block(
                    block.name, vector_havoc.var_name(), vector_havoc
                )

            non_vector_havocs = self.get_non_vector_havocs(loop)
            self.driver.add_var_objects(non_vector_havocs)
            for non_vector_havoc in non_vector_havocs:
                self.store_var_to_block(
                    block.name, non_vector_havoc.var_name(), non_vector_havoc
                )

            havocs = vector_havocs + non_vector_havocs
            inv = self.pred_tracker.invariant(
                inv_name=f"{self.fn_name}_inv{self.loops.index(loop)}",
                args=havocs + self.fn_args,
                writes=havocs,
                reads=self.fn_args,
                grammar=self.inv_grammar,
            )
            blk_state.precond.append(inv.call(blk_state))

        # Visit the block
        self.visit_instructions(block.name, block.instructions)
        blk_state.processed = True

        # If this block is the predecessor of the header of a loop, or the latch of a loop, assert inv
        header_pred_loops = self.find_header_pred_loops(block.name)
        latch_loops = self.find_latch_loops(block.name)
        for loop in header_pred_loops + latch_loops:
            havocs = self.get_vector_havocs(loop) + self.get_non_vector_havocs(loop)
            inv = self.pred_tracker.invariant(
                inv_name=f"{self.fn_name}_inv{self.loops.index(loop)}",
                args=havocs + self.fn_args,
                writes=havocs,
                reads=self.fn_args,
                grammar=self.inv_grammar,
            )
            if len(blk_state.precond) > 0:
                blk_state.asserts.append(
                    implies(and_objects(*blk_state.precond), inv.call(blk_state))
                )
            else:
                blk_state.asserts.append(inv.call(blk_state))

    def visit_instructions(self, block_name: str, instructions: List[ValueRef]) -> None:
        for instr in instructions:
            self.visit_instruction(block_name, instr)

    def visit_alloca_instruction(self, block_name: str, o: ValueRef) -> None:
        # alloca <type>, align <num> or alloca <type>
        t = re.search("alloca ([^$|,]+)", str(o)).group(  # type: ignore
            1
        )  # bug: ops[0] always return i32 1 regardless of type
        # TODO(jie) retire custom list.h interface
        val: Optional[NewObject] = None
        if t == "i32":
            val = IntObject(0)
        elif t == "i8" or t == "i8*":
            val = BoolObject(False)
        elif t == "i1":
            val = BoolObject(False)
        elif t == "%struct.list*":
            val = ListObject[IntObject](IntObject)
        elif t.startswith("%struct.set"):
            # TODO(jie)
            val = Lit(0, SetObject[IntObject])
        elif t.startswith("%struct.tup."):
            # TODO(jie)
            ret_type = [IntObject for _ in range(int(t[-2]) + 1)]
            val = Lit(0, TupleT(*ret_type))
        elif t.startswith("%struct.tup"):
            # TODO(jie)
            val = Lit(0, TupleT(IntObject, IntObject))
        elif t.startswith(
            "%struct."
        ):  # not a tuple or set, assume to be user defined type
            o = re.search("%struct.(.+)", t)
            if o:
                tname = o.group(1)
            else:
                raise Exception("failed to match struct %s: " % t)
            val = ObjectExpr(MLType(tname))
        else:
            raise Exception("NYI: %s" % o)

        # o.name is the register name
        if not o.type.is_pointer:
            self.write_var_to_block(block_name, o.name, val)
        else:
            self.store_var_to_block(block_name, o.name, val)

    def visit_load_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)

        loaded_value = self.load_operand_from_block(block_name, ops[0])
        if not o.type.is_pointer:
            self.write_operand_to_block(block_name, o, loaded_value)
        else:
            self.store_operand_to_block(block_name, o, loaded_value)

    def visit_store_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        value_to_store = None
        if not ops[0].type.is_pointer:
            value_to_store = self.read_operand_from_block(block_name, ops[0])
        else:
            value_to_store = self.load_operand_from_block(block_name, ops[0])
        self.store_operand_to_block(block_name, ops[1], value_to_store)

    def visit_add_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        add_obj = self.read_operand_from_block(
            block_name, ops[0]
        ) + self.read_operand_from_block(block_name, ops[1])
        self.write_operand_to_block(block_name, o, add_obj)

    def visit_sub_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        sub_obj = self.read_operand_from_block(
            block_name, ops[0]
        ) - self.read_operand_from_block(block_name, ops[1])
        self.write_operand_to_block(block_name, o, sub_obj)

    def visit_mul_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        mul_obj = self.read_operand_from_block(
            block_name, ops[0]
        ) * self.read_operand_from_block(block_name, ops[1])
        self.write_operand_to_block(block_name, o, mul_obj)

    def visit_bitcast_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        if not ops[0].type.is_pointer:
            val = self.read_operand_from_block(block_name, ops[0])
            self.write_operand_to_block(block_name, o, val)
        else:
            val = self.load_operand_from_block(block_name, ops[0])
            self.store_operand_to_block(block_name, o, val)

    def visit_sext_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        val = self.read_operand_from_block(block_name, ops[0])
        self.write_operand_to_block(block_name, o, val)

    def visit_icmp_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        cond_match = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(o).strip())
        if cond_match is None:
            raise Exception(f"Failed to match pattern in icmp instruction {o}")
        cond = cond_match.group(1)
        op0 = self.read_operand_from_block(block_name, ops[0])
        op1 = self.read_operand_from_block(block_name, ops[1])
        obj: Optional[BoolObject] = None

        if cond == "eq":
            obj = op0 == op1
        elif cond == "ne":
            obj = (op0 == op1).Not()
        elif cond == "sgt":
            obj = op0 > op1
        elif cond == "sle":
            obj = op0 <= op1
        elif cond == "slt" or cond == "ult":
            obj = op0 < op1
        else:
            raise Exception("NYI %s" % cond)

        self.write_operand_to_block(block_name, o, obj)

    def visit_br_instruction(self, block_name: str, o: ValueRef) -> None:
        ops = list(o.operands)
        if len(ops) > 1:
            # LLVMLite switches the order of branches for some reason
            true_branch = ops[2].name
            false_branch = ops[1].name
            cond = self.read_operand_from_block(block_name, ops[0])
            self.fn_blocks_states[true_branch].precond.append(cond)
            self.fn_blocks_states[false_branch].precond.append(cond.Not())

    def visit_ret_instruction(self, block_name: str, o: ValueRef) -> None:
        # TODO: handle ret void
        blk_state = self.fn_blocks_states[block_name]
        ops = list(o.operands)
        ret_void = len(ops) == 0
        ret_val: Optional[NewObject] = None
        if ret_void and self.fn_sret_arg is not None:
            ret_val = self.fn_sret_arg
        elif not ret_void:
            if not ops[0].type.is_pointer:
                ret_val = self.read_operand_from_block(block_name, ops[0])
            else:
                ret_val = self.load_operand_from_block(block_name, ops[0])
        else:
            raise Exception("ret void not supported yet!")
        # TODO(jie) use the call method of the predicate
        ps = call(
            self.pred_tracker.predicates[self.fn_name].name,
            BoolObject,
            *self.fn_args,
            ret_val,
        )
        if blk_state.precond:
            blk_state.asserts.append(implies(and_objects(*blk_state.precond), ps))
        else:
            blk_state.asserts.append(ps)
        print(f"ps: {blk_state.asserts[-1]}")
        blk_state.has_returned = True

    def visit_call_instruction(self, block_name: str, o: ValueRef) -> None:

        blk_state = self.fn_blocks_states[block_name]
        ops = list(o.operands)
        fn_name = get_fn_name_from_call_instruction(o)

        if fn_name in models.fn_models:
            # TODO(colin): handle global var
            # last argument is ValuRef of arguments to call and is used to index into primitive and pointer variable, format need to match
            # process the mangled name -> name, type
            rv = models.fn_models[fn_name](
                blk_state.primitive_vars, blk_state.pointer_vars, {}, *ops[:-1]
            )

            if rv.val is not None and o.name != "":
                if not o.type.is_pointer:
                    self.write_operand_to_block(
                        block_name=block_name, op=o, val=rv.val
                    )  # primitive
                else:
                    self.store_operand_to_block(
                        block_name=block_name, op=o, val=rv.val
                    )  # pointer
            if rv.assigns:
                for name, value, location in rv.assigns:
                    # TODO: better way to differentiate between writing to primitive vs writing to pointer var
                    if location == "primitive":
                        self.write_var_to_block(
                            block_name=block_name, var_name=name, val=value  # primitive
                        )
                    else:
                        self.store_var_to_block(
                            block_name=block_name, var_name=name, val=value  # pointer
                        )


class Driver:
    var_tracker: VariableTracker
    pred_tracker: PredicateTracker
    asserts: List[NewObject]
    postconditions: List[NewObject]
    fns: Dict[str, "MetaliftFunc"]  # maps analyzed function names to returned object
    target_fn: Callable[[], List[FnDecl]]

    def __init__(self) -> None:
        self.asserts = []
        self.postconditions = []
        self.fns = dict()
        self.var_tracker = VariableTracker()
        self.pred_tracker = PredicateTracker(self)

    def __post_init__(self) -> None:
        print("post init")
        self.var_tracker = VariableTracker(self)
        self.pred_tracker = PredicateTracker(self)

    def variable(self, name: str, type: MLType) -> Var:
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
        llvm_filepath: str,
        loops_filepath: str,
        fn_name: str,
        target_lang_fn: Callable[[], List[FnDecl]],
        inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
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
        vc = and_objects(*self.asserts).src

        target = []
        for fn in self.fns.values():
            target += fn.target_lang_fn()
        # TODO(jie) investigate why set(self.var_tracker.all()) makes things wrong
        synthesized: List[FnDeclRecursive] = run_synthesis(
            "test", target, self.var_tracker.all(), synths, [], vc, synths, "cvc5"
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

    def add_precondition(self, e: NewObject) -> None:
        # this gets propagated to the State when it is created
        self.postconditions.append(e)


class MetaliftFunc:
    driver: Driver
    fn_name: str
    fn_type: MLType
    fn_args: List[ValueRef]
    fn_sret_arg: ValueRef
    fn_blocks: Dict[str, Block]

    target_lang_fn: Callable[[], List[FnDecl]]
    inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject]
    synthesized: Optional[NewObject]

    loops: List[LoopInfo]

    def __init__(
        self,
        driver: Driver,
        llvm_filepath: str,
        loops_filepath: str,
        fn_name: str,
        target_lang_fn: Callable[[], List[FnDecl]],
        inv_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
        ps_grammar: Callable[[NewObject, List[NewObject], List[NewObject]], NewObject],
    ) -> None:
        self.driver = driver
        self.fn_name = fn_name

        # Try to find the function reference in compiled LLVM IR code
        with open(llvm_filepath, mode="r") as file:
            ref = llvm.parse_assembly(file.read())
        functions = list(ref.functions)
        # raw_fn_name is potentially-mangled name of fn_name
        fn_ref: Optional[ValueRef] = None
        for func in functions:
            demangled_name = get_demangled_name(func.name)
            if fn_name == demangled_name:
                fn_ref = ref.get_function(func.name)
        if fn_ref is None:
            raise Exception(
                f"Did not find function declaration for {fn_name} in {llvm_filepath}"
            )

        # Set up blocks
        self.fn_blocks = setupBlocks(fn_ref.blocks)

        # Find the return type of function, and set self.fn_type
        return_type, self.fn_sret_arg = find_return_type_and_sret_arg(
            fn_ref, self.fn_blocks.values()
        )
        self.fn_args = list(filter(lambda arg: not is_sret_arg(arg), fn_ref.arguments))
        fn_args_types = [parse_type_ref_to_obj(a.type) for a in self.fn_args]
        self.fn_type = FnT(return_type, *fn_args_types)

        # Parse and process object functions
        parse_object_func(self.fn_blocks)

        self.target_lang_fn = target_lang_fn
        self.inv_grammar = inv_grammar
        self.ps_grammar = ps_grammar
        self.synthesized = None

        # Parse and process loops
        raw_loops: List[RawLoopInfo] = parse_loops(loops_filepath, fn_ref.name)
        self.loops = [
            LoopInfo.from_raw_loop_info(raw_loop, self.fn_blocks)
            for raw_loop in raw_loops
        ]

    def __call__(self, *args: NewObject, **kwds: Any) -> Any:
        # Check that the arguments passed in have the same names and types as the function definition.
        num_actual_args, num_expected_args = len(args), len(list(self.fn_args))
        if num_expected_args != num_actual_args:
            raise RuntimeError(
                f"expect {num_expected_args} args passed to {self.fn_name} got {num_actual_args} instead"
            )
        for i in range(len(args)):
            passed_in_arg_name, passed_in_arg_type = args[i].var_name(), args[i].type
            fn_arg_name, fn_arg_type = self.fn_args[i].name, self.fn_type.args[1:][i]
            if passed_in_arg_name != fn_arg_name:
                raise Exception(
                    f"Expecting the {i}th argument to have name {fn_arg_name} but instead got {passed_in_arg_name}"
                )
            if passed_in_arg_type != fn_arg_type:
                raise RuntimeError(
                    f"expect {fn_arg_name} to have type {fn_arg_type} rather than {passed_in_arg_type}"
                )

        if self.fn_sret_arg is not None:
            sret_obj_type = parse_type_ref_to_obj(self.fn_sret_arg.type)
            sret_obj = create_object(sret_obj_type, self.fn_sret_arg.name)
        else:
            sret_obj = None

        v = VCVisitor(
            driver=self.driver,
            fn_name=self.fn_name,
            fn_type=self.fn_type,
            fn_args=list(args),
            fn_sret_arg=sret_obj,
            var_tracker=self.driver.var_tracker,
            pred_tracker=self.driver.pred_tracker,
            inv_grammar=self.inv_grammar,
            ps_grammar=self.ps_grammar,
            loops=self.loops,
        )

        # Visit blocks in a DAG order
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

        object_type = self.fn_type.args[0]
        ret_val = create_object(object_type, f"{self.fn_name}_rv")
        self.driver.add_var_object(ret_val)

        # TODO(jie) instead of constructin this call manually can we replace it with a method call.
        ps = call(f"{self.fn_name}_ps", BoolObject, ret_val, *args)

        self.driver.postconditions.append(ps)

        for block in self.fn_blocks.values():
            self.driver.asserts.extend(v.fn_blocks_states[block.name].asserts)

        return ret_val

    T = TypeVar("T")

    def codegen(self, codegen_fn: Callable[[NewObject], T]) -> T:
        if self.synthesized is None:
            raise Exception(f"{self.fn_name} is not synthesized yet")
        else:
            return codegen_fn(self.synthesized)

from multiprocessing.sharedctypes import Value
from llvmlite import binding as llvm
from llvmlite.binding import ValueRef

from typing import Callable, Dict, List, Optional, Set, Union, Tuple, final

from metalift.analysis import LoopInfo, parseLoops
from metalift.ir import (
    And,
    Bool,
    BoolLit,
    Call,
    Eq,
    Expr,
    Implies,
    Int,
    IntLit,
    Type,
    Var,
    parseTypeRef,
)
from metalift import ir


def format_with_index(a: str, idx: int) -> str:
    if idx == 0:
        return a
    else:
        return f"{a}_{idx}"


class VariableTracker(object):
    groups: Dict[str, int] = dict()
    existing: Dict[str, int] = dict()
    var_to_type: Dict[str, Type] = dict()

    def __init__(self) -> None:
        return

    def group(self, name: str) -> "VariableGroup":
        if name in self.groups:
            self.groups[name] += 1
        else:
            self.groups[name] = 0
        return VariableGroup(self, format_with_index(name, self.groups[name]))

    def variable(self, name: str, type: Type) -> Expr:
        if name in self.existing:
            self.existing[name] += 1
        else:
            self.existing[name] = 0

        self.var_to_type[format_with_index(name, self.existing[name])] = type

        return Var(format_with_index(name, self.existing[name]), type)

    def all(self) -> List[Expr]:
        return [Var(name, self.var_to_type[name]) for name in self.var_to_type]


class VariableGroup(object):
    def __init__(self, tracker: VariableTracker, name: str):
        self.tracker = tracker
        self.name = name

    def existing_variable(self, name: str, type: Type) -> Expr:
        my_name = f"{self.name}_{name}"

        if my_name not in self.tracker.existing:
            raise Exception(f"Variable {my_name} does not exist")
        else:
            if self.tracker.existing[my_name] > 0:
                raise Exception(f"There are multiple instances of variable {my_name}")

        assert (
            self.tracker.var_to_type[
                format_with_index(my_name, self.tracker.existing[my_name])
            ]
            == type
        )
        return Var(format_with_index(my_name, self.tracker.existing[my_name]), type)

    def variable_or_existing(self, name: str, type: Type) -> Expr:
        my_name = f"{self.name}_{name}"
        if my_name not in self.tracker.existing:
            self.tracker.existing[my_name] = 0
            self.tracker.var_to_type[
                format_with_index(my_name, self.tracker.existing[my_name])
            ] = type
        else:
            if self.tracker.existing[my_name] > 0:
                raise Exception(f"There are multiple instances of variable {my_name}")

        assert (
            self.tracker.var_to_type[
                format_with_index(my_name, self.tracker.existing[my_name])
            ]
            == type
        )
        return Var(format_with_index(my_name, self.tracker.existing[my_name]), type)

    def variable(self, name: str, type: Type) -> Expr:
        my_name = f"{self.name}_{name}"
        if my_name in self.tracker.existing:
            self.tracker.existing[my_name] += 1
        else:
            self.tracker.existing[my_name] = 0

        self.tracker.var_to_type[
            format_with_index(my_name, self.tracker.existing[my_name])
        ] = type
        return Var(format_with_index(my_name, self.tracker.existing[my_name]), type)


# may or may not participate in a loop
class RawBlock(object):
    name: str
    instructions: List[ValueRef]
    successors: Set[str] = set()

    def __init__(self, name: str, instructions: List[ValueRef]) -> None:
        self.name = name
        self.instructions = instructions

        # extract successors
        final_instruction = instructions[-1]
        final_opcode = final_instruction.opcode
        final_operands = list(final_instruction.operands)

        if final_opcode == "br":
            if len(final_operands) == 1:  # unconditional branch
                targets = [final_operands[0]]
            else:
                targets = final_operands[1:]
        elif final_opcode == "switch":
            targets = final_operands[1::2]
        elif final_opcode == "ret":
            targets = []
        else:
            raise Exception("Unknown end block inst: %s" % final_instruction)

        self.successors = set([t.name for t in targets])

    def rich(
        self, other_blocks: Dict[str, "RawBlock"], loop_info: Dict[str, LoopInfo]
    ) -> "RichBlock":
        part_of_loops = set()
        for loop_head, loop in loop_info.items():
            if self.name in loop.body or self.name in loop.latches:
                part_of_loops.add(loop_head)

        predecessors = set()
        for block in other_blocks.values():
            if self.name in block.successors:
                predecessors.add(block.name)

        return RichBlock(
            self.name, self.instructions, part_of_loops, predecessors, self.successors
        )

    def __repr__(self) -> str:
        pretty_instructions = "; ".join([str(i).strip() for i in self.instructions])
        return f"{self.name}: {pretty_instructions} -> {self.successors}"

    def __str__(self) -> str:
        pretty_instructions = "\n".join([str(i).strip() for i in self.instructions])
        return f"{self.name}:\n{pretty_instructions}\n-> {self.successors}"


# tracks current values of _mutable_ variables
StackEnv = Dict[str, Union[ValueRef, Expr]]


def gen_value(value: ValueRef, fn_group: VariableGroup) -> Expr:
    if value.name:
        return fn_group.existing_variable(value.name, parseTypeRef(value.type))
    elif str(value) == "i32 0":
        return IntLit(0)
    else:
        raise Exception("Cannot generate value for %s" % value)


def gen_expr(expr: ValueRef, fn_group: VariableGroup, env: StackEnv) -> Expr:
    opcode = expr.opcode
    operands = list(expr.operands)
    if opcode == "load":
        # TODO(shadaj): handle situations where the load results in a pointer
        return env[operands[0].name]
    elif opcode == "add":
        return ir.Add(
            gen_value(operands[0], fn_group), gen_value(operands[1], fn_group)
        )
    elif opcode == "mul":
        return ir.Mul(
            gen_value(operands[0], fn_group), gen_value(operands[1], fn_group)
        )
    else:
        raise Exception("Unknown opcode: %s" % opcode)


class RichBlock(object):
    name: str
    instructions: List[ValueRef]
    # loop blocks that may have been executed _before_ this node is reached
    # there is always at least one node that branches to a loop but the loop
    # is not in this set, these nodes determine whether the loop is reached
    part_of_loops: Set[str]

    predecessors: Set[str]
    successors: Set[str]

    vc_condition_cache: Optional[Tuple[Expr, StackEnv]] = None

    def __init__(
        self,
        name: str,
        instructions: List[ValueRef],
        part_of_loops: Set[str],
        predecessors: Set[str],
        successors: Set[str],
    ) -> None:
        self.name = name
        self.instructions = instructions
        self.part_of_loops = part_of_loops
        self.predecessors = predecessors
        self.successors = successors

    def gen_instruction(
        self,
        instruction: ValueRef,
        fn_group: VariableGroup,
        env: StackEnv,
        all_blocks: Dict[str, "RichBlock"],
        next: Callable[..., Expr],
    ) -> Tuple[Optional[Expr], StackEnv]:
        operands = list(instruction.operands)
        if len(instruction.name) > 0:
            if instruction.opcode == "alloca":
                # TODO(shadaj): parseTypeRef silently erases all levels of pointer indirection
                stack_var = fn_group.variable(
                    f"stack_{self.name}_{instruction.name}",
                    parseTypeRef(instruction.type),
                )
                new_env = dict(env)
                new_env[instruction.name] = stack_var
                return (None, new_env)
            else:
                return (
                    Eq(
                        fn_group.variable_or_existing(
                            instruction.name, parseTypeRef(instruction.type)
                        ),
                        gen_expr(instruction, fn_group, env),
                    ),
                    env,
                )
        elif instruction.opcode == "store":
            value = gen_value(operands[0], fn_group)
            stack_target = operands[1].name
            stack_var = fn_group.variable(
                f"stack_{self.name}_{stack_target}", parseTypeRef(operands[1].type)
            )

            updated_stack = dict(env)
            updated_stack[stack_target] = stack_var

            return (Eq(stack_var, value), updated_stack)
        else:
            raise Exception("Unknown instruction: %s" % instruction)

    def gen_jump(
        self,
        instruction: ValueRef,
        fn_group: VariableGroup,
        env: StackEnv,
        all_blocks: Dict[str, "RichBlock"],
        next: Callable[..., Expr],
    ) -> Expr:
        opcode = instruction.opcode
        operands = list(instruction.operands)
        if opcode == "ret":
            return next(
                fn_group.existing_variable(
                    operands[0].name, parseTypeRef(operands[0].type)
                )
            )
        else:
            raise Exception("Unknown jump instruction: %s" % instruction)

    def vc_condition(
        self,
        fn_group: VariableGroup,
        all_blocks: Dict[str, "RichBlock"],
        next: Callable[..., Expr],
    ) -> Tuple[Expr, StackEnv]:
        if self.vc_condition_cache is not None:
            return self.vc_condition_cache

        stack_env = dict()
        for pred in self.predecessors:
            _, pred_stack = all_blocks[pred].vc_condition(fn_group, all_blocks, next)
            for key in pred_stack:
                if key not in stack_env:
                    stack_env[key] = pred_stack[key]
                else:
                    raise Exception("Merging stack variables not yet implemented")

        assigns = []
        for i in self.instructions[:-1]:
            expr, stack_env = self.gen_instruction(
                i, fn_group, stack_env, all_blocks, next
            )
            if expr:
                assigns.append(expr)

        out = (
            Implies(
                And(*assigns),
                self.gen_jump(
                    self.instructions[-1], fn_group, stack_env, all_blocks, next
                ),
            ),
            stack_env,
        )

        self.vc_condition_cache = out
        return out

    def __repr__(self) -> str:
        pretty_instructions = "; ".join([str(i).strip() for i in self.instructions])
        return f"{self.name} (in loops {self.part_of_loops}): {pretty_instructions}"

    def __str__(self) -> str:
        pretty_instructions = "\n".join([str(i).strip() for i in self.instructions])
        return f"{self.name} (in loops {self.part_of_loops}):\n{pretty_instructions}"


class LoopBlock(RichBlock):
    # loop invariant when entering this block, given the current stack environment
    invariant: Optional[Callable[[StackEnv], Expr]]

    def __init__(
        self,
        name: str,
        instructions: List[ValueRef],
        part_of_loops: Set[str],
        predecessors: Set[str],
        successors: Set[str],
    ) -> None:
        super().__init__(name, instructions, part_of_loops, predecessors, successors)

    # TODO(shadaj): vc condition that overrides stack env for variables written here


class AnalysisResult(object):
    arguments: List[ValueRef]
    blocks: Dict[str, RichBlock]
    loop_info: Dict[str, LoopInfo]

    def __init__(
        self,
        arguments: List[ValueRef],
        blocks: Dict[str, RawBlock],
        loop_info: Dict[str, LoopInfo],
    ) -> None:
        self.arguments = arguments
        self.blocks = {
            name: block.rich(blocks, loop_info) for name, block in blocks.items()
        }
        self.loop_info = loop_info

    def call(
        self, *args: Expr
    ) -> Callable[[VariableTracker, Callable[..., Expr]], Expr]:
        def wrapper(tracker: VariableTracker, next: Callable[..., Expr]) -> Expr:
            group = tracker.group("fn")
            arg_variables = {
                arg.name: group.variable(arg.name, parseTypeRef(arg.type))
                for arg in self.arguments
            }
            bb_variables = {b: group.variable(b, Bool()) for b in self.blocks.keys()}
            return Implies(
                And(
                    *[
                        Eq(arg_variables[arg.name], args[i])
                        for i, arg in enumerate(self.arguments)
                    ]
                ),
                Implies(
                    And(
                        *[
                            Eq(
                                bb_variables[b],
                                self.blocks[b].vc_condition(group, self.blocks, next)[
                                    0
                                ],
                            )
                            for b in self.blocks.keys()
                        ]
                    ),
                    bb_variables["bb"],
                ),
            )

        return wrapper


def analyze(
    filename: str,
    fnName: str,
    loopsFile: str,
) -> AnalysisResult:
    with open(filename, mode="r") as file:
        ref = llvm.parse_assembly(file.read())

    fn = ref.get_function(fnName)
    blocks = {
        block.name: RawBlock(block.name, list(block.instructions))
        for block in fn.blocks
    }
    loop_info_list = parseLoops(loopsFile, fnName, log=False)
    loop_info_dict = {}
    for loop in loop_info_list:
        # TODO(shadaj): I believe there is always only one header
        # see https://llvm.org/docs/LoopTerminology.html
        assert len(loop.header) == 1
        loop_info_dict[loop.header[0]] = loop

    return AnalysisResult(list(fn.arguments), blocks, loop_info_dict)


if __name__ == "main":
    test_analysis = analyze("tests/fma_dsl.ll", "test", "tests/fma_dsl.loops")
    for block in test_analysis.blocks.values():
        print(block)
        print()

    variable_tracker = VariableTracker()
    base = Var("base", Int())
    arg1 = Var("arg1", Int())
    base2 = Var("base2", Int())
    arg2 = Var("arg2", Int())

    vc = test_analysis.call(base, arg1, base2, arg2)(
        variable_tracker, lambda ret: Eq(ret, IntLit(0))
    )
    print(vc)

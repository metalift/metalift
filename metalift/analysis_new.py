# # may or may not participate in a loop
# class RawBlock(object):
#     name: str
#     instructions: List[ValueRef]
#     successors: Set[str]
#     return_type: Optional[ObjectT] = None

#     def __init__(self, name: str, instructions: List[ValueRef]) -> None:
#         self.name = name
#         self.instructions = instructions
#         self.successors = set()

#         # extract successors
#         final_instruction = instructions[-1]
#         final_opcode = final_instruction.opcode
#         final_operands = list(final_instruction.operands)

#         if final_opcode == "br":
#             if len(final_operands) == 1:  # unconditional branch
#                 targets = [final_operands[0]]
#             else:
#                 targets = final_operands[1:]
#         elif final_opcode == "switch":
#             targets = final_operands[1::2]
#         elif final_opcode == "ret":
#             targets = []
#             self.return_type = parse_type_ref_to_obj(final_operands[0].type)
#         else:
#             raise Exception("Unknown end block inst: %s" % final_instruction)

#         self.successors = set([t.name for t in targets])

#     def rich(
#         self, other_blocks: Dict[str, "RawBlock"], loop_info: Dict[str, LoopInfo]
#     ) -> "RichBlock":
#         part_of_loops = set()
#         for loop_head, loop in loop_info.items():
#             if self.name in loop.body or self.name in loop.latches:
#                 part_of_loops.add(loop_head)

#         predecessors = set()
#         for block in other_blocks.values():
#             if self.name in block.successors:
#                 predecessors.add(block.name)

#         return RichBlock(
#             self.name, self.instructions, part_of_loops, predecessors, self.successors
#         )

#     def __repr__(self) -> str:
#         pretty_instructions = "; ".join([str(i).strip() for i in self.instructions])
#         return f"{self.name}: {pretty_instructions} -> {self.successors}"

#     def __str__(self) -> str:
#         pretty_instructions = "\n".join([str(i).strip() for i in self.instructions])
#         return f"{self.name}:\n{pretty_instructions}\n-> {self.successors}"


# # tracks current values of _mutable_ variables
# StackEnv = Dict[str, Union[ValueRef, Expr]]


# def gen_value(value: ValueRef, fn_group: VariableGroup) -> Expr:
#     if value.name:
#         return fn_group.existing_variable(value.name, parse_type_ref_to_obj(value.type))
#     elif str(value).startswith("i32 "):
#         literal = int(re.match("i32 (\d+)", str(value).strip()).group(1))  # type: ignore
#         return ir.IntLit(literal)
#     else:
#         raise Exception("Cannot generate value for %s" % value)


# def gen_expr(expr: ValueRef, fn_group: VariableGroup, env: StackEnv) -> Expr:
#     opcode = expr.opcode
#     operands = list(expr.operands)
#     if opcode == "load":
#         # TODO: handle situations where the load results in a pointer
#         return env[operands[0].name]
#     elif opcode == "add":
#         return ir.Add(
#             gen_value(operands[0], fn_group), gen_value(operands[1], fn_group)
#         )
#     elif opcode == "sub":
#         return ir.Sub(
#             gen_value(operands[0], fn_group), gen_value(operands[1], fn_group)
#         )
#     elif opcode == "mul":
#         return ir.Mul(
#             gen_value(operands[0], fn_group), gen_value(operands[1], fn_group)
#         )
#     elif opcode == "icmp":
#         cond = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(expr).strip()).group(1)  # type: ignore
#         op1 = gen_value(operands[0], fn_group)
#         op2 = gen_value(operands[1], fn_group)

#         if cond == "eq":
#             return ir.Eq(op2, op1)
#         elif cond == "sgt":
#             return ir.Lt(op2, op1)
#         elif cond == "sle":
#             return ir.Le(op1, op2)
#         elif cond == "slt" or cond == "ult":
#             return ir.Lt(op1, op2)
#         else:
#             raise Exception("Unknown comparison operator %s" % cond)
#     # elif opcode == "call":
#     #     fnName = operands[-1] if isinstance(operands[-1], str) else operands[-1].name
#     #     if fnName == "":
#     #         # TODO: this is a hack around LLVM bitcasting the function before calling it on aarch64
#     #         fnName = str(operands[-1]).split("@")[-1].split(" ")[0]
#     #     if fnName in models_new.fn_models:
#     #         return models_new.fn_models[fnName](
#     #             [gen_value(arg, fn_group) for arg in operands[:-1]]
#     #         )
#     #     else:
#     #         raise Exception("Unknown function %s" % fnName)
#     else:
#         raise Exception("Unknown opcode: %s" % opcode)


# class RichBlock(object):
#     name: str
#     instructions: List[ValueRef]
#     # loop blocks that may have been executed _before_ this node is reached
#     # there is always at least one node that branches to a loop but the loop
#     # is not in this set, these nodes determine whether the loop is reached
#     part_of_loops: Set[str]

#     predecessors: Set[str]
#     successors: Set[str]

#     vc_condition_cache: Optional[Tuple[Expr, StackEnv]] = None

#     def __init__(
#         self,
#         name: str,
#         instructions: List[ValueRef],
#         part_of_loops: Set[str],
#         predecessors: Set[str],
#         successors: Set[str],
#     ) -> None:
#         self.name = name
#         self.instructions = instructions
#         self.part_of_loops = part_of_loops
#         self.predecessors = predecessors
#         self.successors = successors

#     def gen_instruction(
#         self,
#         instruction: ValueRef,
#         fn_group: VariableGroup,
#         env: StackEnv,
#         all_blocks: Dict[str, "RichBlock"],
#         next: Callable[[Expr], Expr],
#     ) -> Tuple[Optional[Expr], StackEnv]:
#         operands = list(instruction.operands)
#         if len(instruction.name) > 0:
#             if instruction.opcode == "alloca":
#                 # TODO: parseTypeRef silently erases all levels of pointer indirection
#                 stack_var = fn_group.variable(
#                     f"stack_{self.name}_{instruction.name}",
#                     parse_type_ref_to_obj(instruction.type),
#                 )
#                 new_env = dict(env)
#                 new_env[instruction.name] = stack_var
#                 return (None, new_env)
#             else:
#                 return (
#                     Eq(
#                         fn_group.variable_or_existing(
#                             instruction.name, parse_type_ref_to_obj(instruction.type)
#                         ),
#                         gen_expr(instruction, fn_group, env),
#                     ),
#                     env,
#                 )
#         elif instruction.opcode == "store":
#             value = gen_value(operands[0], fn_group)
#             stack_target = operands[1].name
#             stack_var = fn_group.variable(
#                 f"stack_{self.name}_{stack_target}",
#                 parse_type_ref_to_obj(operands[1].type),
#             )

#             updated_stack = dict(env)
#             updated_stack[stack_target] = stack_var

#             return (Eq(stack_var, value), updated_stack)
#         else:
#             raise Exception("Unknown instruction: %s" % instruction)

#     def gen_jump(
#         self,
#         instruction: ValueRef,
#         fn_group: VariableGroup,
#         env: StackEnv,
#         all_blocks: Dict[str, "RichBlock"],
#         next: Callable[[Expr], Expr],
#     ) -> Expr:
#         opcode = instruction.opcode
#         operands = list(instruction.operands)
#         if opcode == "ret":
#             return next(gen_value(operands[0], fn_group))
#         elif opcode == "br":
#             # TODO: invoke invariant if target is loop header we are part of
#             if len(operands) == 1:  # unconditional branch
#                 return Implies(
#                     fn_group.variable_or_existing(
#                         f"{operands[0].name}_from_{self.name}", Bool
#                     ),
#                     fn_group.existing_variable(operands[0].name, Bool),
#                 )
#             else:
#                 condition = gen_value(operands[0], fn_group)

#                 # LLVMLite switches the order of branches for some reason
#                 true_branch = operands[2].name
#                 false_branch = operands[1].name

#                 return ir.Ite(
#                     condition,
#                     Implies(
#                         fn_group.variable_or_existing(
#                             f"{true_branch}_from_{self.name}", Bool
#                         ),
#                         fn_group.existing_variable(true_branch, Bool),
#                     ),
#                     Implies(
#                         fn_group.variable_or_existing(
#                             f"{false_branch}_from_{self.name}", Bool
#                         ),
#                         fn_group.existing_variable(false_branch, Bool),
#                     ),
#                 )
#         else:
#             raise Exception("Unknown jump instruction: %s" % instruction)

#     def vc_condition(
#         self,
#         fn_group: VariableGroup,
#         all_blocks: Dict[str, "RichBlock"],
#         next: Callable[[Expr], Expr],
#     ) -> Tuple[Expr, StackEnv]:
#         if self.vc_condition_cache is not None:
#             return self.vc_condition_cache

#         stack_env = dict()

#         # tracks the which branch variables will result in each distinct merged value
#         # we organize things this way to eliminate redundant merges
#         stack_merges: Dict[Tuple[str, Expr], List[Expr]] = dict()
#         for pred in self.predecessors:
#             _, pred_stack = all_blocks[pred].vc_condition(fn_group, all_blocks, next)
#             for key in pred_stack:
#                 key_expr_pair = (key, pred_stack[key])
#                 if key_expr_pair not in stack_merges:
#                     stack_merges[key_expr_pair] = []

#                 stack_merges[key_expr_pair].append(
#                     fn_group.variable_or_existing(f"{self.name}_from_{pred}", Bool)
#                 )

#         assigns: List[Expr] = []
#         for key, expr in stack_merges:
#             if len(stack_merges[(key, expr)]) == len(self.predecessors):
#                 stack_env[key] = expr
#             else:
#                 if key not in stack_env:
#                     stack_env[key] = fn_group.variable(
#                         f"stack_{self.name}_merge_{key}", pred_stack[key].type
#                     )

#                 for cond in stack_merges[(key, expr)]:
#                     assigns.append(Implies(cond, Eq(stack_env[key], expr)))

#         for i in self.instructions[:-1]:
#             maybe_expr, stack_env = self.gen_instruction(
#                 i, fn_group, stack_env, all_blocks, next
#             )
#             if maybe_expr:
#                 assigns.append(maybe_expr)

#         out = (
#             Implies(
#                 And(*assigns) if len(assigns) > 0 else ir.BoolLit(True),
#                 self.gen_jump(
#                     self.instructions[-1], fn_group, stack_env, all_blocks, next
#                 ),
#             ),
#             stack_env,
#         )

#         self.vc_condition_cache = out
#         return out

#     def __repr__(self) -> str:
#         pretty_instructions = "; ".join([str(i).strip() for i in self.instructions])
#         return f"{self.name} (in loops {self.part_of_loops}): {pretty_instructions}"

#     def __str__(self) -> str:
#         pretty_instructions = "\n".join([str(i).strip() for i in self.instructions])
#         return f"{self.name} (in loops {self.part_of_loops}):\n{pretty_instructions}"


# class LoopBlock(RichBlock):
#     # loop invariant when entering this block, given the current stack environment
#     invariant: Optional[Callable[[StackEnv], Expr]]

#     def __init__(
#         self,
#         name: str,
#         instructions: List[ValueRef],
#         part_of_loops: Set[str],
#         predecessors: Set[str],
#         successors: Set[str],
#     ) -> None:
#         super().__init__(name, instructions, part_of_loops, predecessors, successors)

#     # TODO: vc condition that overrides stack env for variables written here


# class AnalysisResult(object):
#     name: str
#     arguments: List[Var]
#     return_type: ObjectT
#     blocks: Dict[str, RawBlock]
#     loop_info: Dict[str, LoopInfo]

#     def __init__(
#         self,
#         name: str,
#         arguments: List[ValueRef],
#         blocks: Dict[str, RawBlock],
#         loop_info: Dict[str, LoopInfo],
#     ) -> None:
#         self.name = name
#         self.arguments = [
#             Var(arg.name, parse_type_ref_to_obj(arg.type)) for arg in arguments
#         ]
#         self.blocks = blocks

#         found_return = None
#         for block in blocks.values():
#             if block.return_type:
#                 if found_return:
#                     assert found_return == block.return_type
#                 found_return = block.return_type
#         self.return_type = found_return  # type: ignore

#         self.loop_info = loop_info

#     def call(
#         self, *args: Expr
#     ) -> Callable[[VariableTracker, Callable[[Expr], Expr]], Expr]:
#         def wrapper(tracker: VariableTracker, next: Callable[[Expr], Expr]) -> Expr:
#             rich_blocks = {
#                 name: block.rich(self.blocks, self.loop_info)
#                 for name, block in self.blocks.items()
#             }

#             group = tracker.group("fn")
#             arg_variables = {
#                 arg.name(): group.variable(arg.name(), arg.type)
#                 for arg in self.arguments
#             }
#             bb_variables = {b: group.variable(b, Bool) for b in rich_blocks.keys()}
#             return Implies(
#                 And(
#                     *[
#                         Eq(arg_variables[arg.name()], args[i])
#                         for i, arg in enumerate(self.arguments)
#                     ]
#                 )
#                 if len(self.arguments) > 0
#                 else ir.BoolLit(True),
#                 Implies(
#                     And(
#                         *[
#                             Eq(
#                                 bb_variables[b],
#                                 rich_blocks[b].vc_condition(group, rich_blocks, next)[
#                                     0
#                                 ],
#                             )
#                             for b in rich_blocks.keys()
#                         ]
#                     ),
#                     bb_variables["entry"],
#                 ),
#             )

#         return wrapper


# def analyze(
#     filename: str,
#     fnName: str,
#     loopsFile: str,
# ) -> AnalysisResult:
#     with open(filename, mode="r") as file:
#         ref = llvm.parse_assembly(file.read())

#     fn = ref.get_function(fnName)
#     blocks = {
#         block.name: RawBlock(block.name, list(block.instructions))
#         for block in fn.blocks
#     }
#     loop_info_list = parseLoops(loopsFile, fnName, log=False)
#     loop_info_dict = {}
#     for loop in loop_info_list:
#         # TODO: I believe there is always only one header
#         # see https://llvm.org/docs/LoopTerminology.html
#         assert len(loop.header) == 1
#         loop_info_dict[loop.header[0]] = loop

#     return AnalysisResult(fn.name, list(fn.arguments), blocks, loop_info_dict)

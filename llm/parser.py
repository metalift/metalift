import copy
import json
import re
from functools import lru_cache
from pathlib import Path
from textwrap import dedent
from typing import Optional, Type, Union, cast, get_args

from mypy import build
from mypy.defaults import PYTHON3_VERSION
from mypy.modulefinder import BuildSource
from mypy.nodes import (
    AssignmentStmt,
    Block,
    CallExpr,
    ComparisonExpr,
    ConditionalExpr,
    FuncDef,
    IfStmt,
    IndexExpr,
    IntExpr,
    LambdaExpr,
    ListComprehension,
    ListExpr,
    MemberExpr,
    MypyFile,
    NameExpr,
    Node,
    OpExpr,
    ReturnStmt,
    SliceExpr,
    UnaryExpr,
)
from mypy.options import Options
from mypy.types import AnyType, CallableType, Instance
from mypy.types import Type as MypyType
from mypy.types import TypeList, UnboundType

from metalift.ir import (
    Add,
    And,
    Bool,
    Div,
    Eq,
    Expr,
    FnDeclRecursive,
    Ge,
    Gt,
    Int,
    Le,
    List,
    Lt,
    Mod,
    Mul,
    Not,
    Object,
    ObjectT,
    Or,
    Sub,
    call,
    create_object,
    fn_decl_recursive,
    is_fn_decl_type,
    is_list_type,
    is_matrix_type,
    is_nested_list_type,
    ite,
    make_fn_type,
)

TENSPILER_LLM_PATH = Path(__file__).parent.resolve()


def mypy_type_to_ir_type(mypy_type: Optional[MypyType]) -> Optional[ObjectT]:
    """Convert mypy type to python type"""
    if isinstance(mypy_type, UnboundType):
        if mypy_type.optional:
            raise Exception("Optional type not supported")
        if mypy_type.name == "int":
            return Int
        if mypy_type.name == "bool":
            return Bool
        if mypy_type.name == "Any":
            # This means that no types are enforced
            return None
        elif mypy_type.name in {"List", "list"} and len(mypy_type.args) == 1:
            element_type = mypy_type_to_ir_type(mypy_type.args[0])
            return List[element_type]
        elif mypy_type.name == "Callable":
            if len(mypy_type.args) != 2:
                raise Exception("Callable type must have two arguments")
            if not isinstance(mypy_type.args[0], TypeList):
                raise Exception("First argument of Callable type must be a list")
            ret_type = mypy_type_to_ir_type(mypy_type.args[1])
            arg_types = (mypy_type_to_ir_type(arg) for arg in mypy_type.args[0].items)
            return make_fn_type(ret_type, *arg_types)
    elif isinstance(mypy_type, Instance):
        if mypy_type.type.fullname == "builtins.int":
            return Int
        elif mypy_type.type.fullname == "builtins.bool":
            return Bool
        elif mypy_type.type.fullname == "builtins.list":
            return List[mypy_type_to_ir_type(mypy_type.args[0])]
    elif isinstance(mypy_type, CallableType):
        arg_types = (mypy_type_to_ir_type(arg) for arg in mypy_type.arg_types)
        ret_type = mypy_type_to_ir_type(mypy_type.ret_type)
        return make_fn_type(ret_type, *arg_types)
    elif isinstance(mypy_type, AnyType):
        return None
    elif mypy_type is None:
        return None
    else:
        raise Exception(f"{mypy_type} is not supported")


def _get_func_def_arg_names(func_def: FuncDef) -> list[str]:
    return [arg.variable.name for arg in func_def.arguments]


@lru_cache(maxsize=None)
def get_dsl_func_defs() -> List[FuncDef]:
    """
    Get the function definitions of the python dsl module.
    This is cached because the dsl file never changes.
    """
    options = Options()
    options.incremental = False  # turn off caching of previously typed results
    options.show_traceback = True
    options.python_version = PYTHON3_VERSION
    options.preserve_asts = True
    options.export_types = True
    mypy_build = build.build(
        sources=[BuildSource(path=None, module="llm.dsl")],
        options=options,
    )
    python_dsl_tree: MypyFile = cast(
        MypyFile, mypy_build.graph["llm.dsl"].tree
    )  # tree of the entire module / file

    # Get function signatures of the python dsl module
    dsl_func_defs = [
        func_def for func_def in python_dsl_tree.defs if isinstance(func_def, FuncDef)
    ]
    return dsl_func_defs


def mypy_parse(
    code: str, expected_num_funcs: int = 1
) -> tuple[list[FuncDef], dict[str, list[ObjectT]], dict[Node, MypyType]]:
    options = Options()
    # Incremental mode so we don't build the dsl code every time
    options.incremental = True
    options.show_traceback = True
    options.python_version = PYTHON3_VERSION
    options.preserve_asts = True
    options.export_types = True
    mypy_build = build.build(
        sources=[
            BuildSource(path=None, module="target_code", text=code),
            BuildSource(path=None, module="llm.dsl"),
        ],
        options=options,
    )
    target_tree: MypyFile = cast(MypyFile, mypy_build.graph["target_code"].tree)

    # Get target function definition
    target_func_defs = [
        func_def for func_def in target_tree.defs if isinstance(func_def, FuncDef)
    ]
    if len(target_func_defs) != expected_num_funcs:
        raise Exception(
            f"Only rewrite the given {expected_num_funcs} functions and don't include any additional functions"
        )

    # We reject functions that don't have type information in the signature
    func_sign: dict[str, tuple[Type | None, ObjectT | None, list[str]]] = {}
    for func_def in [*target_func_defs, *get_dsl_func_defs()]:
        func_ir_type = mypy_type_to_ir_type(func_def.type)
        if func_ir_type is None:
            raise Exception(f"Function {func_def.name} has no type information")

        arg_ir_types = func_ir_type.argument_types(get_args(func_ir_type))
        ret_ir_type = func_ir_type.return_type(get_args(func_ir_type))
        if any(arg_ir_types) is None:
            raise Exception(
                f"Function {func_def.name} has arguments with no type information"
            )
        if ret_ir_type is None:
            raise Exception(f"Function {func_def.name} has no return type information")

        func_sign[func_def.name] = (
            # use .arg_types to get the argument types and .ret_type for return type
            func_def.type,
            func_ir_type,
            _get_func_def_arg_names(func_def),
        )

    return target_func_defs, func_sign, mypy_build.types


def remove_comments(python_code):
    # Regular expression to match single-line comments
    single_line_comment_pattern = r"#.*?$"

    # Regular expression to match multi-line comments
    multi_line_comment_pattern = r'(\'\'\'[\s\S]*?\'\'\'|"""[\s\S]*?""")'

    # Remove single-line comments
    code_without_single_line_comments = re.sub(
        single_line_comment_pattern, "", python_code, flags=re.MULTILINE
    )

    # Remove multi-line comments
    code_without_comments = re.sub(
        multi_line_comment_pattern, "", code_without_single_line_comments
    )

    return code_without_comments


def _simplify_type_name(type_name: str) -> str:
    if type_name == "builtins.int" or "Literal" in type_name:
        return "integer"
    elif type_name == "builtins.bool":
        return "boolean"
    elif type_name == "builtins.list[builtins.int]":
        return "a list of integers"
    elif type_name == "builtins.list[builtins.list[builtins.int]]":
        return "a list of lists of integers"
    else:
        raise Exception(f"Type {type_name} cannot be simplified to natural language")


def mypy_node_to_ir(
    root_node: Node,
    func_sign: dict[str, list[Union[Type, type]]],
    types: dict[Node, MypyType],
    fn_decls: list[FnDeclRecursive],
    in_calls: list[tuple[str, str]],
    lambda_exprs: dict[Expr, str],
    arg_name_to_count: dict[str, int],
) -> Expr:
    def parse_node(node: Node) -> Expr:
        # TODO: add support for non-lambda inline functions
        if isinstance(node, FuncDef) or isinstance(node, LambdaExpr):
            if isinstance(node, FuncDef):
                _, func_ir_type, _ = func_sign[node.name]
            else:
                func_ir_type = mypy_type_to_ir_type(types[node])
            arg_ir_types = func_ir_type.argument_types(get_args(func_ir_type))
            ret_ir_type = func_ir_type.return_type(get_args(func_ir_type))
            # Create one variable for each argument
            variables: list[Object] = []
            for arg, ir_type in zip(node.arguments, arg_ir_types):
                variables.append(create_object(ir_type, arg.variable.name))
            if isinstance(node, FuncDef):
                # Sort the variables by name so that the order is consistent
                variables = sorted(variables, key=lambda x: x.var_name())
            # Because we are not sure if the function is recursive, we opt to always use the recursive definition
            # If the function is expressed as a lambda expression, then the name will be "<lambda>"
            return fn_decl_recursive(
                node.name,
                ret_ir_type,
                parse_node(node.body),
                *variables,
            )
        elif isinstance(node, Block):
            if len(node.body) == 2:
                if not isinstance(node.body[0], AssignmentStmt):
                    raise Exception(
                        "If the rewritten function has two statements, the first statement must be an assignment to the return value"
                    )
                if not isinstance(node.body[1], ReturnStmt):
                    raise Exception(
                        "If the rewritten function two statements, the second statement must be a return statement"
                    )

                first_stmt = cast(AssignmentStmt, node.body[0])
                second_stmt = cast(ReturnStmt, node.body[1])
                if len(first_stmt.lvalues) != 1:
                    raise Exception(
                        "Only one variable can be on the left side of an assignment"
                    )
                if not isinstance(first_stmt.lvalues[0], NameExpr):
                    raise Exception("Only variables can be assigned to")
                if not isinstance(second_stmt.expr, NameExpr):
                    raise Exception("Only variables can be returned")
                if first_stmt.lvalues[0].name != second_stmt.expr.name:
                    raise Exception(
                        "Return variable must be the same as the variable assigned"
                    )
                return parse_node(first_stmt.rvalue)
            elif len(node.body) == 1:
                return parse_node(node.body[0])
            else:
                raise Exception(
                    f"A function can only have one or two statements, but {root_node.name} has {len(node.body)}"
                )
        elif isinstance(node, ReturnStmt):
            return parse_node(node.expr)
        elif isinstance(node, CallExpr):
            if isinstance(node.callee, MemberExpr):
                # TODO: here we need to identify the list append calls, etc
                raise Exception("Method calls not supported")
            elif isinstance(node.callee, NameExpr):
                func_name = cast(NameExpr, node.callee).name

                # First we check if this function is a python built-in function
                if func_name == "len":
                    if len(node.args) != 1:
                        raise Exception("len() takes exactly one argument")
                    arg_expr = parse_node(node.args[0])
                    if is_matrix_type(arg_expr.type) or is_nested_list_type(
                        arg_expr.type
                    ):
                        list_func_name = "matrix_length"
                    else:
                        list_func_name = "list_length"
                    return call(list_func_name, Int, arg_expr).src

                # Then check if this functino is in our DSL.
                if func_name not in func_sign.keys():
                    raise Exception(f"Function {func_name} is not supported")

                func_type, func_ir_type, arg_names = func_sign[func_name]
                ret_ir_type = func_ir_type.return_type(get_args(func_ir_type))
                arguments_ir_types = func_ir_type.argument_types(get_args(func_ir_type))

                # Check number of arguments
                actual_num_args = len(node.args)
                expected_num_args = len(func_type.arg_names)
                if actual_num_args != expected_num_args:
                    raise Exception(
                        f"Incorrect number of arguments for function {func_name}. Required {expected_num_args} but got {actual_num_args}"
                    )

                # Check argument types and make argument objects
                arg_exprs: List[Expr] = []
                for idx, (arg, expected_ir_type, expected_type) in enumerate(
                    zip(node.args, arguments_ir_types, func_type.arg_types)
                ):
                    # We check if the IR types match but throw errors with python types.
                    # This is because multiple python types can map to the same IR type.
                    arg_expr = parse_node(arg)
                    if arg_expr.type != expected_ir_type:
                        raise Exception(
                            f"{func_name} expects {_simplify_type_name(str(expected_type))} for the {idx}th argument but got {_simplify_type_name(str(types[arg]))}"
                        )

                    # If the argument is a function, then we need to define another function for it
                    if is_fn_decl_type(arg_expr.type):
                        if isinstance(arg, LambdaExpr):
                            if arg_expr in lambda_exprs:
                                arg_fn_name = lambda_exprs[arg_expr]
                            else:
                                arg_name_count = arg_name_to_count.get(
                                    arg_names[idx], 0
                                )
                                arg_fn_name = f"{arg_names[idx]}_{arg_name_count}"
                                arg_name_to_count[arg_names[idx]] = arg_name_count + 1
                                lambda_exprs[arg_expr] = arg_fn_name
                            arg_expr = copy.deepcopy(arg_expr)
                            arg_expr.set_name(arg_fn_name)
                        elif isinstance(arg, NameExpr):
                            arg_fn_name = cast(NameExpr, arg).name
                        else:
                            raise Exception(
                                f"Function argument must be a lambda expression or a function name, but {arg.name} is of type {arg.type}"
                            )
                        fn_decls.append(arg_expr)
                        in_calls.append((func_name, arg_fn_name))
                    arg_exprs.append(arg_expr)

                # Check return type. Again we compare IR types but throw errors using python types.
                actual_ret_ir_type = mypy_type_to_ir_type(types[node])
                if actual_ret_ir_type != ret_ir_type:
                    raise Exception(
                        f"Expected return type {func_type.ret_type} but got {types[node]} for {func_name}"
                    )
                return call(func_name, ret_ir_type, *arg_exprs).src
        elif isinstance(node, NameExpr):
            # Nothing can go wrong with a name expression (which are basically variables)
            ir_type = mypy_type_to_ir_type(types[node])
            return create_object(ir_type, node.name).src
        # TODO: check not
        elif isinstance(node, OpExpr):
            left_expr = parse_node(node.left)
            right_expr = parse_node(node.right)
            op = node.op
            if left_expr.type is Int and right_expr.type is Int:
                if op == "+":
                    return Add(left_expr, right_expr)
                elif op == "-":
                    return Sub(left_expr, right_expr)
                elif op == "*":
                    return Mul(left_expr, right_expr)
                elif op in {"//", "/"}:
                    return Div(left_expr, right_expr)
                elif op == "%":
                    return Mod(left_expr, right_expr)
                else:
                    raise Exception(f"{op} is not supported on integers")
            elif (
                is_list_type(left_expr.type)
                and not is_nested_list_type(left_expr.type)
                and is_list_type(right_expr.type)
                and not is_nested_list_type(right_expr.type)
            ):
                if op == "+":
                    return call("list_concat", List[Int], left_expr, right_expr)
                else:
                    raise Exception(
                        f"Binary operation is not supported {op} on types {types[node.left]} and {types[node.right]}"
                    )
            elif left_expr.type is Bool and right_expr.type is Bool:
                if op == "and":
                    return And(left_expr, right_expr)
                elif op == "or":
                    return Or(left_expr, right_expr)
                else:
                    raise Exception(f"{op} is not supported on booleans")
            else:
                raise Exception(
                    f"Binary operation {op} is not supported on types {types[node.left]} and {types[node.right]}"
                )
        elif isinstance(node, UnaryExpr):
            if node.op == "-":
                node_expr = parse_node(node.expr)
                if node_expr.type is not Int:
                    raise Exception(
                        f"Unary operator - is only supported on integers, not {types[node]}"
                    )
                return Sub(Int(0), node_expr)
            else:
                raise Exception(f"Unary operator {node.op} is not supported")
        elif isinstance(node, IntExpr):
            return create_object(Int, node.value).src
        elif isinstance(node, ListExpr):
            node_type = mypy_type_to_ir_type(types[node])
            return node_type.empty(get_args(node_type)[0]).src
        elif isinstance(node, ConditionalExpr):
            return ite(
                parse_node(node.cond),
                parse_node(node.if_expr),
                parse_node(node.else_expr),
            ).src
        elif isinstance(node, ComparisonExpr):
            clauses: list[Expr] = []
            for i in range(len(node.operators)):
                op = node.operators[i]
                left_node, right_node = node.operands[i], node.operands[i + 1]
                left_expr, right_expr = parse_node(left_node), parse_node(right_node)
                if op == "==":
                    if left_expr.type != right_expr.type:
                        raise Exception(
                            f"Comparison operator {op} only supported on objects of the same type, but got {types[left_node]} and {types[right_node]}"
                        )
                    clauses.append(Eq(left_expr, right_expr))
                else:
                    if left_expr.type is not Int or right_expr.type is not Int:
                        raise Exception(
                            f"Comparison operator {op} only supported on integers, but got {types[left_node]} and {types[right_node]}"
                        )
                    if op == ">":
                        clauses.append(Gt(left_expr, right_expr))
                    elif op == "<":
                        clauses.append(Lt(left_expr, right_expr))
                    elif op == ">=":
                        clauses.append(Ge(left_expr, right_expr))
                    elif op == "<=":
                        clauses.append(Le(left_expr, right_expr))
                    elif op == "!=":
                        clauses.append(Not(Eq(left_expr, right_expr)))
                    else:
                        raise Exception(f"{op} is not supported")
            if len(clauses) == 1:
                return clauses[0]
            else:
                return And(*clauses)
        elif isinstance(node, IndexExpr):
            base_expr = parse_node(node.base)
            base_object = create_object(base_expr.type, base_expr)
            if isinstance(node.index, SliceExpr):
                # Parse begin index
                if node.index.begin_index is None:
                    begin_index = None
                else:
                    begin_index = parse_node(node.index.begin_index)

                # Parse end index
                if node.index.end_index is None:
                    end_index = None
                else:
                    end_index = parse_node(node.index.end_index)

                if begin_index is None and end_index is not None:
                    return base_object[:end_index].src
                elif begin_index is not None and end_index is None:
                    return base_object[begin_index:].src
                elif begin_index is not None and end_index is not None:
                    return base_object[begin_index:end_index].src
                else:
                    raise Exception(
                        f"Slicing index {node.index} is not supported. The only supported slices are [i:], [:j], [i:j]"
                    )
            else:
                index_expr = parse_node(node.index)
                return base_object[index_expr].src
        else:
            if isinstance(node, ListComprehension):
                raise Exception("List comprehensions are not supported")
            elif isinstance(node, IfStmt):
                raise Exception("If statements are not supported")
            raise Exception(f"Unsupported node {node}")

    ps_fn_decl = parse_node(root_node)
    fn_decls.append(ps_fn_decl)


def check_solution(
    *,
    solution: str,
    expected_num_funcs: int,
    dsl_code: str,
    lambda_exprs: dict[Expr, str],
    arg_name_to_count: dict[str, int],
) -> tuple[list[str], list[FnDeclRecursive], dict[str, list[tuple[str, str]]]]:
    universal_imports = "from typing import Any, Callable, List\n"
    dsl_imports = "from llm.dsl import *\n"
    with open(TENSPILER_LLM_PATH / "dsl.py", "w") as f:
        dsl_code_with_imports = dedent(
            remove_comments(dedent(universal_imports) + dedent(dsl_code))
        )
        f.write(dsl_code_with_imports)
    full_prog = dedent(
        remove_comments(universal_imports + dsl_imports + dedent(solution))
    )
    target_func_defs, func_sigs, types = mypy_parse(full_prog, expected_num_funcs)
    fn_decls: list[FnDeclRecursive] = []
    in_calls: list[tuple[str, str]] = []

    for target_func_def in target_func_defs:
        mypy_node_to_ir(
            target_func_def,
            func_sigs,
            types,
            fn_decls,
            in_calls,
            lambda_exprs,
            arg_name_to_count,
        )
    target_func_names = [func_def.name for func_def in target_func_defs]
    return target_func_names, fn_decls, in_calls


def check_solutions(json_filename: str, expected_num_funcs: int = 1) -> None:
    with open(json_filename, "r") as f:
        all_solutions = json.load(f)

    for benchmark_name, benchmark_solutions in all_solutions.items():
        solutions_seen = set()
        for idx, solution in enumerate(benchmark_solutions):
            if solution in solutions_seen:
                print(f"Duplicate solution {idx} for {benchmark_name}")
                continue
            print(solution)

            try:
                check_solution(solution, expected_num_funcs)
                print(f"Solution {idx} for {benchmark_name} is correct")
            except Exception as e:
                print(f"Error in solution {idx} for {benchmark_name}")
                print(e)

            print("\n")
            print("============================================")
            print("\n")
            solutions_seen.add(solution)

import re
import uuid
from typing import Dict
from typing import List as pyList
from typing import Optional
from typing import Tuple as pyTuple
from typing import Type, Union, cast, get_args

from mypy import build
from mypy.defaults import PYTHON3_VERSION
from mypy.modulefinder import BuildSource
from mypy.nodes import (
    Block,
    CallExpr,
    ComparisonExpr,
    ConditionalExpr,
    FuncDef,
    IntExpr,
    LambdaExpr,
    ListExpr,
    MemberExpr,
    MypyFile,
    NameExpr,
    Node,
    OpExpr,
    ReturnStmt,
)
from mypy.options import Options
from mypy.types import AnyType, CallableType, Instance
from mypy.types import Type as MypyType
from mypy.types import TypeList, UnboundType

from metalift.ir import (
    Bool,
    Eq,
    Expr,
    Fn,
    FnDeclRecursive,
    Ge,
    Gt,
    Int,
    Le,
    List,
    Lt,
    Object,
    ObjectT,
    call,
    create_object,
    fn_decl_recursive,
    is_fn_decl_type,
    ite,
)


def mypy_type_to_ir_type(mypy_type: MypyType) -> Optional[ObjectT]:
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
        elif mypy_type.name == "List" and len(mypy_type.args) == 1:
            return List[mypy_type_to_ir_type(mypy_type.args[0])]
        elif mypy_type.name == "Callable":
            assert len(mypy_type.args) == 2
            assert isinstance(mypy_type.args[0], TypeList)
            ret_type = mypy_type_to_ir_type(mypy_type.args[1])
            arg_types = (mypy_type_to_ir_type(arg) for arg in mypy_type.args[0].items)
            return Fn[pyTuple[(ret_type, *arg_types)]]
    elif isinstance(mypy_type, Instance):
        if mypy_type.type.fullname == "builtins.int":
            return Int
        elif mypy_type.type.fullname == "builtins.list":
            return List[mypy_type_to_ir_type(mypy_type.args[0])]
    elif isinstance(mypy_type, CallableType):
        arg_types = (mypy_type_to_ir_type(arg) for arg in mypy_type.arg_types)
        ret_type = mypy_type_to_ir_type(mypy_type.ret_type)
        return Fn[pyTuple[(ret_type, *arg_types)]]
    elif isinstance(mypy_type, AnyType):
        return None
    raise Exception(f"Unsupported type {mypy_type}")


def mypy_type_to_python_type(mypy_type: MypyType) -> Optional[Type]:
    ir_type = mypy_type_to_ir_type(mypy_type)
    if ir_type is None:
        return None
    else:
        return ir_type.to_python_type(get_args(ir_type))


# Ordered dict
def _get_func_def_ir_type(func_def: FuncDef) -> Type[Fn]:
    arg_types = [
        mypy_type_to_ir_type(arg.type_annotation) for arg in func_def.arguments
    ]
    ret_type = mypy_type_to_ir_type(func_def.type.ret_type)
    return Fn[pyTuple[(ret_type, *arg_types)]]


def _get_func_def_arg_names(func_def: FuncDef) -> pyList[str]:
    return [arg.variable.name for arg in func_def.arguments]


# TODO(jie): add return type
def mypy_parse(
    code: str,
) -> pyTuple[FuncDef, Dict[str, List[ObjectT]], Dict[Node, MypyType]]:
    options = Options()
    options.incremental = False  # turn off caching of previously typed results
    # options.export_types = True
    options.show_traceback = True
    options.python_version = PYTHON3_VERSION
    options.preserve_asts = True
    options.export_types = True
    mypy_build = build.build(
        sources=[
            BuildSource(path=None, module="target_code", text=code),
            BuildSource(path=None, module="tenspiler.llm.python_dsl"),
        ],
        options=options,
    )
    target_tree: MypyFile = cast(MypyFile, mypy_build.graph["target_code"].tree)
    python_dsl_tree: MypyFile = cast(
        MypyFile, mypy_build.graph["tenspiler.llm.python_dsl"].tree
    )  # tree of the entire module / file

    # Get target function definition
    target_func_defs = [
        func_def for func_def in target_tree.defs if isinstance(func_def, FuncDef)
    ]
    assert len(target_func_defs) == 1
    target_func_def = target_func_defs[0]
    assert isinstance(target_func_def, FuncDef)

    # Get function signatures of the python dsl module
    dsl_func_defs = [
        func_def for func_def in python_dsl_tree.defs if isinstance(func_def, FuncDef)
    ]

    func_sign = {
        func_def.name: (
            _get_func_def_ir_type(func_def),
            _get_func_def_arg_names(func_def),
        )
        for func_def in [target_func_def, *dsl_func_defs]
    }

    return target_func_def, func_sign, mypy_build.types


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


def mypy_node_to_ir(
    node: Node,
    func_sign: Dict[str, pyList[Union[Type, type]]],
    types: Dict[Node, MypyType],
    fn_decls: pyList[FnDeclRecursive],
    in_calls: pyList[pyTuple[str, str]],
) -> Expr:
    def parse_node(node: Node) -> Expr:
        # TODO(jie): add support for non-lambda inline functions
        if isinstance(node, FuncDef) or isinstance(node, LambdaExpr):
            if isinstance(node, FuncDef):
                func_ir_type, _ = func_sign[node.name]
            else:
                func_ir_type = mypy_type_to_ir_type(types[node])
            arg_ir_types = func_ir_type.argument_types(get_args(func_ir_type))
            ret_ir_type = func_ir_type.return_type(get_args(func_ir_type))
            # Create one variable for each argument
            variables: pyList[Object] = []
            for arg, ir_type in zip(node.arguments, arg_ir_types):
                variables.append(create_object(ir_type, arg.variable.name))
            # Because we are not sure if the function is recursive, we opt to always use the recursive definition
            # If the function is expressed as a lambda expression, then the name will be "<lambda>"
            return fn_decl_recursive(
                node.name,
                ret_ir_type,
                parse_node(node.body),
                *variables,
            )
        elif isinstance(node, Block):
            if len(node.body) > 1:
                raise Exception("Block with more than one statement not supported")
            return parse_node(node.body[0])
        elif isinstance(node, ReturnStmt):
            return parse_node(node.expr)
        elif isinstance(node, CallExpr):
            if isinstance(node.callee, MemberExpr):
                # TODO(jie): here we need to identify the list append calls, etc
                raise Exception("Method calls not supported")
                # mypy_node_to_ir(node.callee, func_sign, types)
            elif isinstance(node.callee, NameExpr):
                func_name = cast(NameExpr, node.callee).name

                # First we check if this function is a python built-in function
                if func_name == "len":
                    if len(node.args) != 1:
                        raise Exception("len() takes exactly one argument")
                    arg_expr = parse_node(node.args[0])
                    if arg_expr.type.is_nested:
                        list_func_name = "matrix_length"
                    else:
                        list_func_name = "list_length"
                    return call(list_func_name, Int, arg_expr)

                # Then check if this functino is in our DSL.
                if func_name not in func_sign.keys():
                    raise Exception(f"Unknown function {func_name}")

                func_ir_type, arg_names = func_sign[func_name]
                ret_ir_type = func_ir_type.return_type(get_args(func_ir_type))
                arguments_ir_types = func_ir_type.argument_types(get_args(func_ir_type))

                # Check number of arguments
                if len(node.args) != len(arguments_ir_types):
                    raise Exception(
                        f"Incorrect number of arguments. Required {len(func_sign[func_name])} but got {len(node.args)}"
                    )

                # Check argument types and make argument objects
                arg_exprs: List[Expr] = []
                for idx, (arg, expected_ir_type) in enumerate(
                    zip(node.args, arguments_ir_types)
                ):
                    arg_expr = parse_node(arg)
                    if arg_expr.type != expected_ir_type:
                        raise Exception(
                            f"Expected type {expected_ir_type} but got {arg_expr.type} for {idx}th argument of {func_name}"
                        )

                    # If the argument is a function, then we need to define another function for it
                    if is_fn_decl_type(arg_expr.type):
                        lambda_fn_name = f"{arg_names[idx]}_{str(uuid.uuid4())[:8]}"
                        arg_expr.set_name(lambda_fn_name)
                        fn_decls.append(arg_expr)
                        in_calls.append((func_name, lambda_fn_name))
                    arg_exprs.append(arg_expr)

                # Check return type
                actual_ret_ir_type = mypy_type_to_ir_type(types.get(node))
                if actual_ret_ir_type != ret_ir_type:
                    raise Exception(
                        f"Expected return type {ret_ir_type} but got {actual_ret_ir_type} for {func_name}"
                    )
                return call(func_name, ret_ir_type, *arg_exprs)
        elif isinstance(node, NameExpr):
            # Nothing can go wrong with a name expression (which are basically variables)
            ir_type = mypy_type_to_ir_type(types[node])
            return create_object(ir_type, node.name)
        elif isinstance(node, OpExpr):
            left = parse_node(node.left)
            right = parse_node(node.right)
            op = node.op
            if left.type is Int and right.type is Int:
                if op == "+":
                    return left + right
                elif op == "-":
                    return left - right
                elif op == "*":
                    return left * right
                elif op == "//":
                    return left // right
                else:
                    raise Exception(f"Unsupported operator {op} on integers")
            else:
                raise Exception(
                    f"Unsupported binary operations {op} on types {left.type} and {right.type}"
                )
        elif isinstance(node, IntExpr):
            return create_object(Int, node.value)
        elif isinstance(node, ListExpr):
            node_type = mypy_type_to_ir_type(types[node])
            return node_type.empty(get_args(node_type)[0])
        elif isinstance(node, ConditionalExpr):
            return ite(
                parse_node(node.cond),
                parse_node(node.if_expr),
                parse_node(node.else_expr),
            ).src
        elif isinstance(node, ComparisonExpr):
            if len(node.operators) != 1:
                raise Exception("Multiple operators not supported")
            if len(node.operands) != 2:
                raise Exception("Operation must be performed on exactly two operands")
            op = node.operators[0]
            left_expr = parse_node(node.operands[0])
            right_expr = parse_node(node.operands[1])
            if left_expr.type is not Int or right_expr.type is not Int:
                raise Exception("Comparison only supported on integers")
            if op == ">":
                return Gt(left_expr, right_expr)
            elif op == "<":
                return Lt(left_expr, right_expr)
            elif op == "==":
                return Eq(left_expr, right_expr)
            elif op == ">=":
                return Ge(left_expr, right_expr)
            elif op == "<=":
                return Le(left_expr, right_expr)
            else:
                raise Exception(f"Unsupported operator {op}")
        else:
            raise Exception(f"Unsupported node {node}")

    ps_fn_decl = parse_node(node)
    fn_decls.append(ps_fn_decl)

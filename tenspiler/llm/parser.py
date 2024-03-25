import ast
import re
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
    FuncDef,
    IntExpr,
    MemberExpr,
    MypyFile,
    NameExpr,
    Node,
    OpExpr,
    ReturnStmt,
)
from mypy.options import Options
from mypy.types import AnyType, Instance
from mypy.types import Type as MypyType
from mypy.types import TypeList, UnboundType

from metalift.ir import (
    Bool,
    Expr,
    Fn,
    Int,
    List,
    Object,
    ObjectT,
    call,
    create_object,
    fn_decl_recursive,
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
        func_def.name: _get_func_def_ir_type(func_def)
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
    func_sign: Dict[str, List[Union[Type, type]]],
    types: Dict[Node, MypyType],
) -> Expr:
    if isinstance(node, FuncDef):
        func_ir_type = func_sign[node.name]
        arg_ir_types = func_ir_type.argument_types(get_args(func_ir_type))
        ret_ir_type = func_ir_type.return_type(get_args(func_ir_type))
        # Create one variable for each argument
        variables: pyList[Object] = []
        for arg, ir_type in zip(node.arguments, arg_ir_types):
            variables.append(create_object(ir_type, arg.variable.name))
        # Because we are not sure if the function is recursive, we opt to always use the recursive definition
        return fn_decl_recursive(
            node.name,
            ret_ir_type,
            mypy_node_to_ir(node.body, func_sign, types),
            *variables,
        )
    elif isinstance(node, Block):
        if len(node.body) > 1:
            raise Exception("Block with more than one statement not supported")
        return mypy_node_to_ir(node.body[0], func_sign, types)
    elif isinstance(node, ReturnStmt):
        return mypy_node_to_ir(node.expr, func_sign, types)
    elif isinstance(node, CallExpr):
        if isinstance(node.callee, MemberExpr):
            # TODO(jie): here we need to identify the list append calls, etc
            raise Exception("Method calls not supported")
            # mypy_node_to_ir(node.callee, func_sign, types)
        elif isinstance(node.callee, NameExpr):
            func_name = cast(NameExpr, node.callee).name
            func_ir_type = func_sign[func_name]
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
                arg_expr = mypy_node_to_ir(arg, func_sign, types)
                if arg_expr.type != expected_ir_type:
                    raise Exception(
                        f"Expected type {expected_ir_type} but got {arg_expr.type} for {idx}th argument of {func_name}"
                    )
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
        left = mypy_node_to_ir(node.left, func_sign, types)
        right = mypy_node_to_ir(node.right, func_sign, types)
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
    else:
        raise Exception(f"Unsupported node {node}")


# TODO(jie): add types
def check_func(tree, func_sign):
    assignments = 0
    for node in ast.walk(tree):
        if isinstance(node, ast.Call):
            # if attribute is present, then it is a method call
            if isinstance(node.func, ast.Attribute):
                print(f"Undefined function {node.func.value.id}.{node.func.attr}")
                return False
            # check if the defined function has correct number of arguments
            if node.func.id in func_sign.keys():
                if len(node.args) != func_sign[node.func.id]:
                    print(
                        f"Incorrect number of arguments. Required {func_sign[node.func.id]} but got {len(node.args)}"
                    )
                    return False
            if node.func.id not in func_sign.keys():
                print(f"Undefined function {node.func.id}")
                return False
        # reject if else block
        if isinstance(node, ast.If):
            print(f"if else block not allowed")
            return False
        # accept only if count of assignments is 1
        if isinstance(node, ast.Assign):
            assignments += 1
            if assignments > 1:
                print(f"Intermediate results not allowed")
                return False
    return True

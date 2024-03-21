import ast
import re
from importlib import import_module
from inspect import getmembers, isfunction
from typing import Callable, Dict, List, Type, Union, cast, get_type_hints

import mypy as mp
from mypy.defaults import PYTHON3_VERSION
from mypy.modulefinder import BuildSource
from mypy.nodes import (
    Block,
    CallExpr,
    FuncDef,
    MemberExpr,
    MypyFile,
    NameExpr,
    Node,
    ReturnStmt,
)
from mypy.options import Options
from mypy.types import Instance
from mypy.types import Type as MypyType
from mypy.types import TypeList, UnboundType


def _mypy_type_to_type(mypy_type: MypyType) -> Type:
    """Convert mypy type to python type"""
    if isinstance(mypy_type, UnboundType):
        if mypy_type.optional:
            raise Exception("Optional type not supported")
        if mypy_type.name == "int":
            return int
        elif mypy_type.name == "List" and len(mypy_type.args) == 1:
            return List[_mypy_type_to_type(mypy_type.args[0])]
        elif mypy_type.name == "Callable":
            assert len(mypy_type.args) == 2
            assert isinstance(mypy_type.args[0], TypeList)
            arg_types = [_mypy_type_to_type(arg) for arg in mypy_type.args[0].items]
            return Callable[arg_types, _mypy_type_to_type(mypy_type.args[1])]
    elif isinstance(mypy_type, Instance):
        if mypy_type.type.fullname == "builtins.int":
            return int
        elif mypy_type.type.fullname == "builtins.list":
            import pdb

            pdb.set_trace()
            return List[_mypy_type_to_type(mypy_type.args[0])]
    raise Exception(f"Unsupported type {mypy_type}")


def _get_arg_types(func_def: FuncDef) -> List[Union[Type, type]]:
    return [_mypy_type_to_type(arg.type_annotation) for arg in func_def.arguments]


# TODO(jie): add return type
def mypy_parse(code: str):
    options = Options()
    options.incremental = False  # turn off caching of previously typed results
    # options.export_types = True
    options.show_traceback = True
    options.python_version = PYTHON3_VERSION
    options.preserve_asts = True
    options.export_types = True
    mypy_build = mp.build.build(
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

    func_sigs = {
        func_def.name: _get_arg_types(func_def)
        for func_def in [target_func_def, *dsl_func_defs]
    }

    return target_func_def, func_sigs, mypy_build.types


def get_module_func_sigs(module_name):
    """Get the function signatures of a module"""
    module = import_module(module_name)
    functions = getmembers(module, isfunction)
    func_sigs: Dict[str, Dict[str, Union[type, Type]]] = {}
    for name, func in functions:
        func_sigs[name] = get_type_hints(func)
    return func_sigs


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


def check_node(
    node: Node,
    func_sign: Dict[str, List[Union[Type, type]]],
    types: Dict[str, MypyType],
):
    if isinstance(node, FuncDef):
        check_node(node.body, func_sign, types)
    elif isinstance(node, Block):
        for stmt in node.body:
            check_node(stmt, func_sign, types)
    elif isinstance(node, ReturnStmt):
        check_node(node.expr, func_sign, types)
    elif isinstance(node, CallExpr):
        if isinstance(node.callee, MemberExpr):
            check_node(node.callee, func_sign, types)
        elif isinstance(node.callee, NameExpr):
            func_name = cast(NameExpr, node.callee).name
            if len(node.args) != len(func_sign[func_name]):
                raise Exception(
                    f"Incorrect number of arguments. Required {len(func_sign[func_name])} but got {len(node.args)}"
                )
            for idx, (arg, expected_type) in enumerate(
                zip(node.args, func_sign[func_name])
            ):
                arg_type = types.get(arg)
                assert arg_type is not None
                if _mypy_type_to_type(arg_type) != expected_type:
                    raise Exception(
                        f"Expected type {expected_type} but got {arg_type} for {idx}th argument of {func_name}"
                    )
                check_node(arg, func_sign, types)
        for arg in node.args:
            check_node(arg, func_sign, types)
    elif isinstance(node, NameExpr):
        # Nothing can go wrong with a name expression (which are basically variables)
        pass
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
                import pdb

                pdb.set_trace()
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

import ast
import re
from importlib import import_module
from inspect import getmembers, isfunction, signature


def import_module_functions(module_name):
    """
    Import all functions from the given module dynamically.

    Args:
    module_name (str): Name of the module.

    Returns:
    dict: Dictionary containing function names as keys and their signatures as values.
    """
    module = import_module(module_name)
    functions = getmembers(module, isfunction)
    function_signatures = {name: signature(func) for name, func in functions}
    return function_signatures


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


funcs = import_module_functions("tenspiler.llm.python_dsl")

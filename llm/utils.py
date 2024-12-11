import re
from dataclasses import dataclass
from typing import Union

from metalift.ir import Object, create_object


@dataclass
class SingleLoopInfo:
    loop_var: Object
    read_vars: list[Object]
    modified_vars: list[Object]


@dataclass
class DoubleLoopInfo:
    outer_loop_var: Object
    inner_loop_var: Object
    outer_loop_read_vars: list[Object]
    inner_loop_read_vars: list[Object]
    outer_loop_modified_vars: list[Object]
    inner_loop_modified_vars: list[Object]


def extract_all_python_functions(s: str) -> list[str]:
    # TODO(sahil): use this instead of the extract function in all models.
    extracted_result = [
        x.group(1)
        for x in re.finditer(
            r"```(?:Python|python|assembly|cpp|c|c\+\+)?(.*?)```", s, re.DOTALL
        )
    ]
    return extracted_result


def replace_ite(ps_sol: str) -> str:
    """Replace ite() with the Python ternary operator."""

    def repl_func(match):
        cond = match.group(1).strip()
        a = match.group(2).strip()
        b = match.group(3).strip()
        return f"{a} if {cond} else {b}"

    ite_pattern = r"ite\(([^,]+),\s*([^,]+),\s*([^)]+)\)"
    return re.sub(ite_pattern, repl_func, ps_sol)


def get_inv_args(
    loop_info: SingleLoopInfo | DoubleLoopInfo,
) -> Union[list[Object], tuple[list[Object], list[Object]]]:
    """Given some loop info, return the invariant arguments."""
    if isinstance(loop_info, SingleLoopInfo):
        vars = sorted(
            list(
                set(
                    [var.src for var in loop_info.read_vars]
                    + [var.src for var in loop_info.modified_vars]
                    + [loop_info.loop_var.src]
                )
            ),
            key=lambda x: x.name(),
        )
        return [create_object(var.type, var.name()) for var in vars]
    else:
        outer_inv_args = sorted(
            list(
                set(
                    [var.src for var in loop_info.outer_loop_read_vars]
                    + [var.src for var in loop_info.outer_loop_modified_vars]
                    + [loop_info.outer_loop_var.src]
                )
            ),
            key=lambda x: x.name(),
        )
        inner_inv_args = sorted(
            list(
                set(
                    [var.src for var in loop_info.inner_loop_read_vars]
                    + [var.src for var in loop_info.inner_loop_modified_vars]
                    + [loop_info.inner_loop_var.src]
                )
            ),
            key=lambda x: x.name(),
        )
        outer_inv_args = [create_object(var.type, var.name()) for var in outer_inv_args]
        inner_inv_args = [create_object(var.type, var.name()) for var in inner_inv_args]
        return outer_inv_args, inner_inv_args


def replace_args(*, args: list[Object], replace_args: dict[str, str]) -> list[Object]:
    """In the given list of args, replace the variable names according to the given `replace_args`."""
    new_args: list[Object] = []
    for arg in args:
        arg_name = replace_args.get(arg.var_name(), arg.var_name())
        new_args.append(create_object(arg.type, arg_name))
    return new_args

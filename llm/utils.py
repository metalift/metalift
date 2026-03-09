import re
from dataclasses import dataclass
from typing import List, Union

from llvmlite.binding import ValueRef

from metalift.analysis import CodeInfo, analyze_demangled
from metalift.ir import Object, create_object, parse_type_ref_to_obj


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


def _codeinfo_var_to_object(v: Union[ValueRef, Object]) -> Object:
    """
    Convert a CodeInfo modified/read var (usually a ValueRef) into a Metalift Object.

    CodeInfo.modified_vars and CodeInfo.read_vars are populated from LLVM ValueRef
    operands (e.g., store targets or function arguments). We recover the type from
    the LLVM type and use the variable name as-is.
    """
    if isinstance(v, Object):
        return v
    if isinstance(v, ValueRef):
        obj_t = parse_type_ref_to_obj(v.type)
        # ValueRef.name may be empty for temporaries; in that case we skip it.
        if v.name == "":
            raise ValueError("Encountered ValueRef without a name in CodeInfo")
        return create_object(obj_t, v.name)
    # Fallback: some CodeInfo entries may be Expr; they should normally not appear
    # in loop CodeInfo.modified_vars/read_vars. If they do, treat their first arg
    # as the variable name and their type as-is.
    if hasattr(v, "type") and hasattr(v, "args"):
        name = v.args[0]
        return create_object(v.type, name)
    raise TypeError(f"Unsupported CodeInfo var of type {type(v)}")


def single_loop_info_from_codeinfo(
    ci: CodeInfo,
    loop_var: Object,
) -> SingleLoopInfo:
    """
    Build a SingleLoopInfo from a legacy CodeInfo instance.

    - loop_var: the induction variable Object (e.g., Int(\"i\")), supplied by the caller.
    - modified_vars: derived from CodeInfo.modified_vars (havoced vars in the loop).
    - read_vars: derived from CodeInfo.read_vars (function arguments).
    """
    modified: List[Object] = []
    for v in ci.modified_vars:
        try:
            obj = _codeinfo_var_to_object(v)
            modified.append(obj)
        except Exception:
            # Be conservative and skip variables we cannot interpret.
            continue

    reads: List[Object] = []
    for v in ci.read_vars:
        try:
            obj = _codeinfo_var_to_object(v)
            reads.append(obj)
        except Exception:
            continue

    return SingleLoopInfo(loop_var=loop_var, read_vars=reads, modified_vars=modified)


def infer_single_loop_info_from_llvm(
    *,
    llvm_filepath: str,
    loops_filepath: str,
    fn_name: str,
    loop_var: Object,
    inv_index: int = 0,
) -> SingleLoopInfo:
    """
    Build SingleLoopInfo by parsing the LLVM file with the new frontend.

    Uses Driver + MetaliftFunc only (no VC), so C++ vector/STL calls in the .ll
    are handled by parse_object_func and do not trigger "NYI" in the legacy VC.

    - fn_name: demangled function name (e.g. "softmax_part1").
    - inv_index: which loop to use (0 = first loop).
    - loop_var: induction variable Object (e.g. Int("i")).
    """
    from metalift.frontend.llvm import Driver

    driver = Driver()
    mf = driver.analyze(
        llvm_filepath=llvm_filepath,
        loops_filepath=loops_filepath,
        fn_name=fn_name,
        target_lang_fn=lambda: [],
        inv_grammars={},
        ps_grammar=None,
    )
    if not mf.loops:
        raise RuntimeError(
            f"No loops found for function {fn_name} in {llvm_filepath}"
        )
    if inv_index < 0 or inv_index >= len(mf.loops):
        raise IndexError(
            f"inv_index {inv_index} out of range for {len(mf.loops)} loops"
        )
    loop = mf.loops[inv_index]
    modified_vars = [
        create_object(parse_type_ref_to_obj(v.type), v.name)
        for v in sorted(loop.havocs, key=lambda x: x.name)
    ]
    read_vars = [
        create_object(mf.fn_args_types[i], mf.fn_args[i].name)
        for i in range(len(mf.fn_args))
    ]
    return SingleLoopInfo(
        loop_var=loop_var,
        modified_vars=modified_vars,
        read_vars=read_vars,
    )

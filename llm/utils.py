import re
import subprocess
from dataclasses import dataclass
from typing import List, Union

from llvmlite.binding import ValueRef

from metalift.analysis import CodeInfo
from metalift.frontend.llvm import Driver
from metalift.ir import Int, Object, create_object, parse_type_ref_to_obj
from tenspiler.tree_parser import (
    find_root_node_from_file,
    get_inner_loop_declared_var_names,
    get_loop_var_names,
)


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


def recreate_loop_info_from_var_map(
    loop_info: SingleLoopInfo | DoubleLoopInfo, var_map: dict
) -> SingleLoopInfo | DoubleLoopInfo:
    """Recreate loop_info using types from var_map (e.g. var_tracker after VC)."""

    def _remap_vars(vars: list[Object]) -> list[Object]:
        return [
            create_object(var_map[var.var_name()].type, var.var_name())
            if var.var_name() in var_map
            else var
            for var in vars
        ]

    if isinstance(loop_info, SingleLoopInfo):
        return SingleLoopInfo(
            loop_var=loop_info.loop_var,
            read_vars=_remap_vars(loop_info.read_vars),
            modified_vars=_remap_vars(loop_info.modified_vars),
        )

    return DoubleLoopInfo(
        outer_loop_var=loop_info.outer_loop_var,
        inner_loop_var=loop_info.inner_loop_var,
        outer_loop_read_vars=_remap_vars(loop_info.outer_loop_read_vars),
        inner_loop_read_vars=_remap_vars(loop_info.inner_loop_read_vars),
        outer_loop_modified_vars=_remap_vars(loop_info.outer_loop_modified_vars),
        inner_loop_modified_vars=_remap_vars(loop_info.inner_loop_modified_vars),
    )


def prepare_loop_info_from_driver(
    loop_info: SingleLoopInfo | DoubleLoopInfo, driver
) -> SingleLoopInfo | DoubleLoopInfo:
    """Recreate loop_info using types from driver's var_tracker (e.g. after VC). Use when loop_info was inferred from LLVM."""
    variables = driver.var_tracker.all()
    var_map = {var.name(): var for var in variables}
    return recreate_loop_info_from_var_map(loop_info, var_map)


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
    driver: "Driver",
    cc_path: str,
    fn_name: str,
) -> SingleLoopInfo:
    """
    Build SingleLoopInfo by parsing the LLVM file with the new frontend.

    Uses Driver + MetaliftFunc only (no VC), so C++ vector/STL calls in the .ll
    are handled by parse_object_func and do not trigger "NYI" in the legacy VC.

    - cc_path: path to the C/C++ source file (e.g. *.cc).
    - fn_name: demangled function name (e.g. "softmax_part1").
    - inv_index: which loop to use (0 = first loop).
    """
    # 1) Ensure the corresponding .ll and .loops files exist by running the
    #    compile-add-blocks helper. This compiles `cc_path` to LLVM, runs the
    #    AddEmptyBlocks pass and loop analysis, and produces *.ll / *.loops.
    subprocess.run(
        ["metalift/utils/llvm/compile-add-blocks", cc_path],
        check=True,
    )

    if cc_path.endswith(".cc"):
        llvm_filepath = cc_path.replace(".cc", ".ll")
        loops_filepath = cc_path.replace(".cc", ".loops")
    else:
        raise ValueError(f"Unsupported file extension: {cc_path}")

    mf = driver.analyze(
        llvm_filepath=llvm_filepath,
        loops_filepath=loops_filepath,
        fn_name=fn_name,
        target_lang_fn=lambda: [],
        inv_grammars={},
        ps_grammar=None,
    )

    if not mf.loops:
        raise RuntimeError(f"No loops found for function {fn_name} in {llvm_filepath}")

    root_node = find_root_node_from_file(cc_path)
    names = get_loop_var_names(root_node)
    # There should be only one loop variable.
    if len(names) != 1:
        raise ValueError(f"Expected 1 loop variable, got {len(names)}")
    loop_var = Int(names[0])

    loop = mf.loops[0]
    modified_vars = [
        create_object(parse_type_ref_to_obj(v.type), v.name)
        for v in sorted(loop.havocs, key=lambda x: x.name)
    ]
    read_vars = [
        create_object(mf.fn_args_types[i], mf.fn_args[i].name)
        for i in range(len(mf.fn_args))
    ]
    loop_info = SingleLoopInfo(
        loop_var=loop_var,
        modified_vars=modified_vars,
        read_vars=read_vars,
    )

    return loop_info


def infer_double_loop_info_from_llvm(
    *,
    driver: "Driver",
    cc_path: str,
    fn_name: str,
) -> DoubleLoopInfo:
    """
    Build DoubleLoopInfo by parsing the LLVM file with the new frontend.

    Uses Driver + MetaliftFunc (same flow as infer_single_loop_info_from_llvm)
    and expects exactly two loop induction variables from source parsing.

    - cc_path: path to the C/C++ source file (e.g. *.cc).
    - fn_name: demangled function name.
    """
    # Ensure corresponding .ll and .loops files are generated.
    subprocess.run(
        ["metalift/utils/llvm/compile-add-blocks", cc_path],
        check=True,
    )

    if cc_path.endswith(".cc"):
        llvm_filepath = cc_path.replace(".cc", ".ll")
        loops_filepath = cc_path.replace(".cc", ".loops")
    else:
        raise ValueError(f"Unsupported file extension: {cc_path}")

    mf = driver.analyze(
        llvm_filepath=llvm_filepath,
        loops_filepath=loops_filepath,
        fn_name=fn_name,
        target_lang_fn=lambda: [],
        inv_grammars={},
        ps_grammar=None,
    )

    if len(mf.loops) != 2:
        raise RuntimeError(
            f"Expected 2 loops for function {fn_name} in {llvm_filepath}, got {len(mf.loops)}"
        )

    root_node = find_root_node_from_file(cc_path)
    names = get_loop_var_names(root_node)
    if len(names) != 2:
        raise ValueError(f"Expected 2 loop variables, got {len(names)}")
    outer_loop_var = Int(names[0])
    inner_loop_var = Int(names[1])

    # Use the first two loops in Metalift's discovered order as outer/inner.
    outer_loop = mf.loops[0]
    inner_loop = mf.loops[1]

    # Outer-loop modified vars should exclude:
    # 1) vars also modified by the inner loop, and
    # 2) loop induction vars.
    inner_havoc_names = {v.name for v in inner_loop.havocs}
    excluded_outer_names = {
        outer_loop_var.var_name(),
        inner_loop_var.var_name(),
        *inner_havoc_names,
    }
    outer_loop_modified_vars = [
        create_object(parse_type_ref_to_obj(v.type), v.name)
        for v in sorted(outer_loop.havocs, key=lambda x: x.name)
        if v.name not in excluded_outer_names
    ]
    inner_declared_names = get_inner_loop_declared_var_names(root_node)
    excluded_inner_names = {inner_loop_var.var_name(), *inner_declared_names}

    inner_loop_modified_vars = [
        create_object(parse_type_ref_to_obj(v.type), v.name)
        for v in sorted(inner_loop.havocs, key=lambda x: x.name)
        if v.name not in excluded_inner_names
    ] + outer_loop_modified_vars

    # Function args are always readable in both loops.
    fn_read_vars = [
        create_object(mf.fn_args_types[i], mf.fn_args[i].name)
        for i in range(len(mf.fn_args))
    ]
    # Inner loop also reads outer-loop context:
    # - outer loop induction var (e.g. row / channel index),
    # - outer-loop-carried modified vars (e.g. partial output/state).
    inner_loop_read_vars = fn_read_vars + [outer_loop_var] + outer_loop_modified_vars
    # Deduplicate by variable name while preserving order.
    inner_loop_read_vars = list(
        {var.var_name(): var for var in inner_loop_read_vars}.values()
    )

    loop_info = DoubleLoopInfo(
        outer_loop_var=outer_loop_var,
        inner_loop_var=inner_loop_var,
        outer_loop_read_vars=fn_read_vars,
        inner_loop_read_vars=inner_loop_read_vars,
        outer_loop_modified_vars=outer_loop_modified_vars,
        inner_loop_modified_vars=inner_loop_modified_vars,
    )
    return loop_info

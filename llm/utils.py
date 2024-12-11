import re


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

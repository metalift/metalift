from metalift.ir import fn_decl
from tenspiler.tenspiler_common import (
    integer_exp_fn_decl,
    integer_sqrt_fn_decl,
    integer_sqrt_helper_fn_decl,
)

fn_decls = [integer_exp_fn_decl, integer_sqrt_helper_fn_decl, integer_sqrt_fn_decl]
with open("integer_fn.smt", "w") as f:
    for fn_decl in fn_decls:
        f.write(fn_decl.toSMT())
    f.write("\n\n")

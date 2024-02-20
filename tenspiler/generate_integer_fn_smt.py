from metalift.ir import Int, call, fn_decl, fn_decl_recursive, ite
from metalift.vc_util import or_objects

n = Int("n")
integer_exp_fn_name = "integer_exp"
integer_exp_body = ite(n <= 0, Int(1), (call(integer_exp_fn_name, Int, n - 1) * 3) % 64)
integer_exp_fn_decl = fn_decl_recursive(integer_exp_fn_name, Int, integer_exp_body, n)

guess = Int("guess")
integer_sqrt_helper_fn_name = "integer_sqrt_helper"
integer_sqrt_helper_body = ite(
    or_objects(guess == 0, guess == 1, guess > 64),
    Int(1),
    ite(
        guess == n // guess,
        guess,
        call(integer_sqrt_helper_fn_name, Int, n, (guess + n // guess) // 2),
    ),
)
integer_sqrt_helper_fn_decl = fn_decl_recursive(
    integer_sqrt_helper_fn_name,
    Int,
    integer_sqrt_helper_body,
    n,
    guess,
)

integer_sqrt_fn_name = "integer_sqrt"
integer_sqrt_fn_decl = fn_decl(
    integer_sqrt_fn_name, Int, call(integer_sqrt_helper_fn_name, Int, n // 2, n), n
)

fn_decls = [integer_exp_fn_decl, integer_sqrt_helper_fn_decl, integer_sqrt_fn_decl]
with open("integer_fn.smt", "w") as f:
    for fn_decl in fn_decls:
        f.write(fn_decl.toSMT())
    f.write("\n\n")

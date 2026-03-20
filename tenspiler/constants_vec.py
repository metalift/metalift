from tenspiler.axioms import (
    reduce_max_axiom,
    reduce_sum_axiom,
    scalar_vec_div_axiom,
    scalar_vec_sub_axiom,
    vec_elemwise_add_axiom,
    vec_elemwise_div_axiom,
    vec_elemwise_mul_axiom,
    vec_elemwise_sub_axiom,
    vec_scalar_add_axiom,
    vec_scalar_div_axiom,
    vec_scalar_mul_axiom,
    vec_scalar_sub_axiom,
)
from tenspiler.tenspiler_common import (
    firsts_fn_decl,
    integer_exp_fn_decl,
    integer_sqrt,
    integer_sqrt_helper_fn_decl,
    ite_int,
    rests_fn_decl,
    scalar_vec_to_vec_target_lang,
    selection_two_args_fn_decl,
    vec_slice_fn_decl,
    vec_to_int_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)

_UNSORTED_TENSPILER_FNS = list(
    set(
        [
            *vec_to_int_target_lang,
            *vec_vec_to_vec_target_lang,
            *scalar_vec_to_vec_target_lang,
            *vec_to_vec_target_lang,
            selection_two_args_fn_decl,
            vec_slice_fn_decl,
            firsts_fn_decl,
            rests_fn_decl,
            integer_exp_fn_decl,
            integer_sqrt_helper_fn_decl,
            integer_sqrt,
            ite_int,
        ]
    )
)
_NOT_NONE_UNSORTED_TENSPILER_FNS = [
    fn for fn in _UNSORTED_TENSPILER_FNS if fn.body() is not None
]
TENSPILER_FNS = sorted(_NOT_NONE_UNSORTED_TENSPILER_FNS, key=lambda x: x.name())
TENSPILER_FN_NAME_TO_AXIOMS = {
    "vec_elemwise_add": [vec_elemwise_add_axiom],
    "vec_elemwise_mul": [vec_elemwise_mul_axiom],
    "scalar_vec_sub": [scalar_vec_sub_axiom],
    "vec_scalar_sub": [vec_scalar_sub_axiom],
    "vec_scalar_add": [vec_scalar_add_axiom],
    "scalar_vec_div": [scalar_vec_div_axiom],
    "vec_scalar_mul": [vec_scalar_mul_axiom],
    "vec_elemwise_sub": [vec_elemwise_sub_axiom],
    "reduce_sum": [reduce_sum_axiom],
    "reduce_max": [reduce_max_axiom],
    "vec_scalar_div": [vec_scalar_div_axiom],
    "vec_elemwise_div": [vec_elemwise_div_axiom],
}

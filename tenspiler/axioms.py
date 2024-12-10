from metalift.ir import Axiom, Bool, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, implies, ite
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_dissolve_matrix_selection,
    call_dissolve_selection,
    call_matrix_elemwise_add,
    call_matrix_elemwise_mul,
    call_matrix_elemwise_sub,
    call_matrix_scalar_div,
    call_matrix_scalar_mul,
    call_matrix_scalar_sub,
    call_matrix_selection,
    call_matrix_vec_mul,
    call_reduce_max,
    call_reduce_sum,
    call_scalar_vec_div,
    call_scalar_vec_sub,
    call_selection,
    call_vec_elemwise_add,
    call_vec_elemwise_div,
    call_vec_elemwise_mul,
    call_vec_elemwise_sub,
    call_vec_scalar_add,
    call_vec_scalar_div,
    call_vec_scalar_mul,
    call_vec_scalar_sub,
)

index = Int("index")
a = mlList(Int, "a")
b = mlList(Int, "b")
i = Int("i")
x = Matrix(Int, "x")
y = Matrix(Int, "y")
opacity = Int("opacity")
rand = Int("rand")


def vec_elemwise_add_axiom(a: mlList[int], b: mlList[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len(), a.len() == b.len()),
        call_vec_elemwise_add(a[:index], b[:index])
        == call_vec_elemwise_add(a[1:index], b[1:index]).prepend(a[0] + b[0]),
    )


def vec_elemwise_mul_axiom(a: mlList[int], b: mlList[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len(), a.len() == b.len()),
        call_vec_elemwise_mul(a[:index], b[:index])
        == call_vec_elemwise_mul(a[1:index], b[1:index]).prepend(a[0] * b[0]),
    )


def scalar_vec_sub_axiom(a: mlList[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len()),
        call_scalar_vec_sub(i, a[:index])
        == call_scalar_vec_sub(i, a[1:index]).prepend(i - a[0]),
    )


def vec_scalar_sub_axiom(a: mlList[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len()),
        call_vec_scalar_sub(i, a[:index])
        == call_vec_scalar_sub(i, a[1:index]).prepend(a[0] - i),
    )


def vec_scalar_add_axiom(a: mlList[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len()),
        call_vec_scalar_add(i, a[:index])
        == call_vec_scalar_add(i, a[1:index]).prepend(i + a[0]),
    )


def scalar_vec_div_axiom(i: int, a: mlList[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len()),
        call_scalar_vec_div(i, a[:index])
        == call_scalar_vec_div(i, a[1:index]).prepend(i // a[0]),
    )


def vec_scalar_mul_axiom(a: mlList[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len()),
        call_vec_scalar_mul(i, a[:index])
        == call_vec_scalar_mul(i, a[1:index]).prepend(i * a[0]),
    )


def vec_elemwise_sub_axiom(a: mlList[int], b: mlList[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len(), a.len() == b.len()),
        call_vec_elemwise_sub(a[:index], b[:index])
        == call_vec_elemwise_sub(a[1:index], b[1:index]).prepend(a[0] - b[0]),
    )


def reduce_sum_axiom(data: mlList[int], index: int, max_pos: int) -> Bool:
    return implies(
        and_objects(index >= 0, index <= max_pos, max_pos >= 0),
        call_reduce_sum(data[: index + 1])
        == call_reduce_sum(data[:index]) + data[index],
    )


def reduce_max_axiom(data: mlList[int], index: int, max_pos: int) -> Bool:
    return implies(
        and_objects(index >= 0, index <= max_pos, max_pos >= 0),
        call_reduce_max(data[: index + 1])
        == ite(
            data[index] > (call_reduce_max(data[:index])),
            data[index],
            (call_reduce_max(data[:index])),
        ),
    )


def vec_scalar_div_axiom(a: mlList[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len()),
        call_vec_scalar_div(i, a[:index])
        == call_vec_scalar_div(i, a[1:index]).prepend(a[0] // i),
    )


def vec_elemwise_div_axiom(a: mlList[int], b: mlList[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < a.len(), a.len() == b.len()),
        call_vec_elemwise_div(a[:index], b[:index])
        == call_vec_elemwise_div(a[1:index], b[1:index]).prepend(a[0] // b[0]),
    )


def matrix_elemwise_add_axiom(x: Matrix[int], y: Matrix[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len(), x.len() == y.len()),
        call_matrix_elemwise_add(x[:index], y[:index])
        == call_matrix_elemwise_add(x[1:index], y[1:index]).prepend(
            call_vec_elemwise_add(x[0], y[0])
        ),
    )


def matrix_elemwise_sub_axiom(x: Matrix[int], y: Matrix[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len(), x.len() == y.len()),
        call_matrix_elemwise_sub(x[:index], y[:index])
        == call_matrix_elemwise_sub(x[1:index], y[1:index]).prepend(
            call_vec_elemwise_sub(x[0], y[0])
        ),
    )


def matrix_scalar_mul_axiom(x: Matrix[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len()),
        call_matrix_scalar_mul(i, x[:index])
        == call_matrix_scalar_mul(i, x[1:index]).prepend(call_vec_scalar_mul(i, x[0])),
    )


def matrix_vec_mul_axiom(x: Matrix[int], b: mlList[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len()),
        call_matrix_vec_mul(x[:index], b)
        == call_matrix_vec_mul(x[1:index], b).prepend(
            call_reduce_sum(call_vec_elemwise_mul(x[0], b))
        ),
    )


def matrix_elemwise_mul_axiom(x: Matrix[int], y: Matrix[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len(), x.len() == y.len()),
        call_matrix_elemwise_mul(x[:index], y[:index])
        == call_matrix_elemwise_mul(x[1:index], y[1:index]).prepend(
            call_vec_elemwise_mul(x[0], y[0])
        ),
    )


def matrix_scalar_div_axiom(x: Matrix[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len()),
        call_matrix_scalar_div(i, x[:index])
        == call_matrix_scalar_div(i, x[1:index]).prepend(call_vec_scalar_div(i, x[0])),
    )


def matrix_scalar_sub_axiom(x: Matrix[int], i: int, index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len()),
        call_matrix_scalar_sub(i, x[:index])
        == call_matrix_scalar_sub(i, x[1:index]).prepend(call_vec_scalar_sub(i, x[0])),
    )


def matrix_selection_two_args_axiom(x: Matrix[int], y: Matrix[int], index: int) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len(), x.len() == y.len()),
        call_matrix_selection(x[:index], y[:index])
        == call_matrix_selection(x[1:index], y[1:index]).prepend(
            call_selection(x[0], y[0])
        ),
    )


def dissolve_matrix_selection_two_args_axiom(
    x: Matrix[int], y: Matrix[int], opacity: int, rand: int, index: int
) -> Bool:
    return implies(
        and_objects(index >= 0, index < x.len(), x.len() == y.len()),
        call_dissolve_matrix_selection(x[:index], y[:index], opacity, rand)
        == call_dissolve_matrix_selection(
            x[1:index], y[1:index], opacity, rand
        ).prepend(call_dissolve_selection(x[0], y[0], opacity, rand)),
    )


vec_elemwise_add_axiom = Axiom(
    vec_elemwise_add_axiom(a, b, index).src, a.src, b.src, index.src
)

vec_elemwise_mul_axiom = Axiom(
    vec_elemwise_mul_axiom(a, b, index).src, a.src, b.src, index.src
)

scalar_vec_sub_axiom = Axiom(
    scalar_vec_sub_axiom(a, i, index).src, a.src, i.src, index.src
)

vec_scalar_sub_axiom = Axiom(
    vec_scalar_sub_axiom(a, i, index).src, a.src, i.src, index.src
)

vec_scalar_add_axiom = Axiom(
    vec_scalar_add_axiom(a, i, index).src, a.src, i.src, index.src
)

scalar_vec_div_axiom = Axiom(
    scalar_vec_div_axiom(i, a, index).src, i.src, a.src, index.src
)

vec_scalar_mul_axiom = Axiom(
    vec_scalar_mul_axiom(a, i, index).src, a.src, i.src, index.src
)

vec_elemwise_sub_axiom = Axiom(
    vec_elemwise_sub_axiom(a, b, index).src, a.src, b.src, index.src
)

reduce_sum_axiom = Axiom(reduce_sum_axiom(a, index, i).src, a.src, index.src, i.src)

reduce_max_axiom = Axiom(reduce_max_axiom(a, index, i).src, a.src, index.src, i.src)

vec_scalar_div_axiom = Axiom(
    vec_scalar_div_axiom(a, i, index).src, a.src, i.src, index.src
)

vec_elemwise_div_axiom = Axiom(
    vec_elemwise_div_axiom(a, b, index).src, a.src, b.src, index.src
)

matrix_elemwise_add_axiom = Axiom(
    matrix_elemwise_add_axiom(x, y, index).src, x.src, y.src, index.src
)

matrix_elemwise_sub_axiom = Axiom(
    matrix_elemwise_sub_axiom(x, y, index).src, x.src, y.src, index.src
)

matrix_scalar_sub_axiom = Axiom(
    matrix_scalar_sub_axiom(x, i, index).src, x.src, i.src, index.src
)

matrix_scalar_mul_axiom = Axiom(
    matrix_scalar_mul_axiom(x, i, index).src, x.src, i.src, index.src
)

matrix_vec_mul_axiom = Axiom(
    matrix_vec_mul_axiom(x, b, index).src, x.src, b.src, index.src
)

matrix_elemwise_mul_axiom = Axiom(
    matrix_elemwise_mul_axiom(x, y, index).src, x.src, y.src, index.src
)

matrix_scalar_div_axiom = Axiom(
    matrix_scalar_div_axiom(x, i, index).src, x.src, i.src, index.src
)

matrix_selection_two_args_axiom = Axiom(
    matrix_selection_two_args_axiom(x, y, index).src, x.src, y.src, index.src
)

dissolve_matrix_selection_two_args_axiom = Axiom(
    dissolve_matrix_selection_two_args_axiom(x, y, opacity, rand, index).src,
    x.src,
    y.src,
    opacity.src,
    rand.src,
    index.src,
)

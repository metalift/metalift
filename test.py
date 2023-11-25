from tests.llvm.gaudi.gaudi_common import get_unique_int_exps_with_depth
from metalift.ir import Int
from tests.python.utils.utils import codegen

all_wrappers = get_unique_int_exps_with_depth(
    args=[Int("x"), Int("y")],
    constants=[Int(255), Int(0)],
    compute_ops=["-", "//"],
    depth=3
)
# for wrapper in all_wrappers[2]:
#     print(codegen(wrapper.object.src))
import pdb; pdb.set_trace()
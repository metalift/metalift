# from typing import Callable, Dict, List
# from metalift.ir import Bool, Call, Expr, Int, IntLit, Ite, SetT

# fn_models: Dict[str, Callable[[List[Expr]], Expr]] = {
#     "set_create": lambda args: Call("set-create", SetT(Int())),
#     "set_add": lambda args: Call(
#         "set-insert",
#         SetT(Int()),
#         args[1],
#         args[0],
#     ),
#     "set_remove": lambda args: Call(
#         "set-minus",
#         SetT(Int()),
#         args[0],
#         Call("set-singleton", SetT(Int()), args[1]),
#     ),
#     "set_contains": lambda args: Ite(
#         Call(
#             "set-member",
#             Bool(),
#             args[1],
#             args[0],
#         ),
#         IntLit(1),
#         IntLit(0),
#     ),
# }

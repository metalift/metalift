from collections import namedtuple
from typing import Callable, Dict

from llvmlite.binding import ValueRef

from metalift.ir import Bool, Call, Expr, Int, IntLit, Ite, SetT, Type, parseTypeRef
from metalift.vc_util import parseOperand

ReturnValue = namedtuple("ReturnValue", ["val", "assigns"])

RegsType = Dict[str, Expr]
GVarsType = Dict[str, str]


def newlist(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    return ReturnValue(Call("list_empty", Type("MLList", Int())), None)


def listLength(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    return ReturnValue(Call("list_length", Int(), regs[args[0].name]), None)


def listGet(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    return ReturnValue(Call("list_get", Int(), regs[args[0].name], regs[args[1].name]), None)


def listAppend(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    return ReturnValue(
        Call("list_append", parseTypeRef(args[0].type), regs[args[0].name], regs[args[1].name]),
        None,
    )


def listConcat(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    return ReturnValue(
        Call("list_concat", parseTypeRef(args[0].type), regs[args[0].name], regs[args[1].name]),
        None,
    )


def newTuple(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    return ReturnValue(Call("newTuple", Type("Tuple", Int(), Int())), None)


def MakeTuple(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    regVals = [regs[args[i].name] for i in range(len(args))]
    retVals = [Int() for i in range(len(args))]
    return ReturnValue(
        Call("make-tuple", Type("Tuple", *retVals), *regVals),
        None,
    )


def tupleGet(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    return ReturnValue(
        Call("tupleGet", Int(), regs[args[0].name], parseOperand(args[1], regs)), None
    )


def getField(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    (fieldName, obj) = args
    val = mem[obj.name].args[fieldName.args[0]]
    # regs[i] = mem[obj].args[fieldName.args[0]
    return ReturnValue(val, None)


def setField(
    regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
) -> ReturnValue:
    (fieldName, obj, val) = args
    mem[obj.name].args[fieldName.args[0]] = regs[val.name]
    # XXX: not tracking memory writes as assigns for now. This might be fine for now since all return vals must be loaded to regs
    return ReturnValue(None, None)


fnModels: Dict[str, Callable[..., ReturnValue]] = {
    # mangled names for non template version of list.h
    # "_Z7newListv": newlist,
    # "_Z10listLengthP4list": listLength,
    # "_Z7listGetP4listi": listGet,
    # "_Z10listAppendP4listi": listAppend
    # mangled names for template version of list.h
    # TODO add mangle name for list_concat
    "_Z7newListIiEP4listIT_Ev": newlist,
    "_Z10listLengthIiEiP4listIT_E": listLength,
    "_Z7listGetIiET_P4listIS0_Ei": listGet,
    "_Z10listAppendIiEP4listIT_ES3_S1_": listAppend,
    "getField": getField,
    "setField": setField,
    # names for set.h
    "set_create": lambda regs, mem, gvars, *args: ReturnValue(
        Call("set-create", SetT(Int())), None
    ),
    "set_add": lambda regs, mem, gvars, *args: ReturnValue(
        Call(
            "set-insert",
            SetT(Int()),
            parseOperand(args[1], regs),
            parseOperand(args[0], regs),
        ),
        None,
    ),
    "set_remove": lambda regs, mem, gvars, *args: ReturnValue(
        Call(
            "set-minus",
            SetT(Int()),
            parseOperand(args[0], regs),
            Call("set-singleton", SetT(Int()), parseOperand(args[1], regs)),
        ),
        None,
    ),
    "set_contains": lambda regs, mem, gvars, *args: ReturnValue(
        Ite(
            Call(
                "set-member",
                Bool(),
                parseOperand(args[1], regs),
                parseOperand(args[0], regs),
            ),
            IntLit(1),
            IntLit(0),
        ),
        None,
    ),
    # mangled names for tuple.h
    "_Z8newTupleIiiEP3tupIT_T0_Ev": newTuple,
    "_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_": MakeTuple,
    "_Z9MakeTupleIJiiiEEP3tupIJDpT_EES2_": MakeTuple,
    "_Z8tupleGetIJiiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
    "_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
    "_ZL8tupleGetIJiiEEDaP3tupIJDpT_EEi": tupleGet,
    "_Z8tupleGetIJiiiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
    # TODO(shadaj): investigate why this is not necessary for all devs
    "_Z8tupleGetIJiiELi0EENSt9enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
}

























# TODO(colin): delete the old implementation when new llvm is ready
# from collections import namedtuple
# from typing import Callable, Dict

# from llvmlite.binding import ValueRef

# from metalift.ir import Bool, Call, Expr, Int, IntLit, Ite, SetT, Type, parseTypeRef
# from metalift.vc_util import parseOperand

# ReturnValue = namedtuple("ReturnValue", ["val", "assigns"])

# RegsType = Dict[ValueRef, Expr]
# GVarsType = Dict[str, str]


# def newlist(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     return ReturnValue(Call("list_empty", Type("MLList", Int())), None)


# def listLength(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     return ReturnValue(Call("list_length", Int(), regs[args[0]]), None)


# def listGet(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     return ReturnValue(Call("list_get", Int(), regs[args[0]], regs[args[1]]), None)


# def listAppend(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     return ReturnValue(
#         Call("list_append", parseTypeRef(args[0].type), regs[args[0]], regs[args[1]]),
#         None,
#     )


# def listConcat(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     return ReturnValue(
#         Call("list_concat", parseTypeRef(args[0].type), regs[args[0]], regs[args[1]]),
#         None,
#     )


# def newTuple(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     return ReturnValue(Call("newTuple", Type("Tuple", Int(), Int())), None)


# def MakeTuple(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     regVals = [regs[args[i]] for i in range(len(args))]
#     retVals = [Int() for i in range(len(args))]
#     return ReturnValue(
#         Call("make-tuple", Type("Tuple", *retVals), *regVals),
#         None,
#     )


# def tupleGet(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     return ReturnValue(
#         Call("tupleGet", Int(), regs[args[0]], parseOperand(args[1], regs)), None
#     )


# def getField(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     (fieldName, obj) = args
#     val = mem[obj].args[fieldName.args[0]]
#     # regs[i] = mem[obj].args[fieldName.args[0]
#     return ReturnValue(val, None)


# def setField(
#     regs: RegsType, mem: RegsType, gvars: GVarsType, *args: ValueRef
# ) -> ReturnValue:
#     (fieldName, obj, val) = args
#     mem[obj].args[fieldName.args[0]] = regs[val]
#     # XXX: not tracking memory writes as assigns for now. This might be fine for now since all return vals must be loaded to regs
#     return ReturnValue(None, None)


# fnModels: Dict[str, Callable[..., ReturnValue]] = {
#     # mangled names for non template version of list.h
#     # "_Z7newListv": newlist,
#     # "_Z10listLengthP4list": listLength,
#     # "_Z7listGetP4listi": listGet,
#     # "_Z10listAppendP4listi": listAppend
#     # mangled names for template version of list.h
#     # TODO add mangle name for list_concat
#     "_Z7newListIiEP4listIT_Ev": newlist,
#     "_Z10listLengthIiEiP4listIT_E": listLength,
#     "_Z7listGetIiET_P4listIS0_Ei": listGet,
#     "_Z10listAppendIiEP4listIT_ES3_S1_": listAppend,
#     "getField": getField,
#     "setField": setField,
#     # names for set.h
#     "set_create": lambda regs, mem, gvars, *args: ReturnValue(
#         Call("set-create", SetT(Int())), None
#     ),
#     "set_add": lambda regs, mem, gvars, *args: ReturnValue(
#         Call(
#             "set-insert",
#             SetT(Int()),
#             parseOperand(args[1], regs),
#             parseOperand(args[0], regs),
#         ),
#         None,
#     ),
#     "set_remove": lambda regs, mem, gvars, *args: ReturnValue(
#         Call(
#             "set-minus",
#             SetT(Int()),
#             parseOperand(args[0], regs),
#             Call("set-singleton", SetT(Int()), parseOperand(args[1], regs)),
#         ),
#         None,
#     ),
#     "set_contains": lambda regs, mem, gvars, *args: ReturnValue(
#         Ite(
#             Call(
#                 "set-member",
#                 Bool(),
#                 parseOperand(args[1], regs),
#                 parseOperand(args[0], regs),
#             ),
#             IntLit(1),
#             IntLit(0),
#         ),
#         None,
#     ),
#     # mangled names for tuple.h
#     "_Z8newTupleIiiEP3tupIT_T0_Ev": newTuple,
#     "_Z9MakeTupleIJiiEEP3tupIJDpT_EES2_": MakeTuple,
#     "_Z9MakeTupleIJiiiEEP3tupIJDpT_EES2_": MakeTuple,
#     "_Z8tupleGetIJiiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
#     "_Z8tupleGetIJiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
#     "_ZL8tupleGetIJiiEEDaP3tupIJDpT_EEi": tupleGet,
#     "_Z8tupleGetIJiiiiELi0EENSt3__19enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
#     # TODO(shadaj): investigate why this is not necessary for all devs
#     "_Z8tupleGetIJiiELi0EENSt9enable_ifIXltT0_sZT_EiE4typeEP3tupIJDpT_EEi": tupleGet,
# }
from collections import namedtuple

from ir import Type, Set, parseTypeRef, Int, Var, Call, IntLit, Ite
from vc_util import parseOperand

ReturnValue = namedtuple("ReturnValue", ["val", "assigns"])


def newlist(regs, *args):
    # return ReturnValue(None, [(args[0], Expr.Pred("list_new", parseTypeRef(args[0].type)))])
    return ReturnValue(Var("list_empty", Type("MLList", Int())), None)


def listLength(regs, *args):
    return ReturnValue(Call("list_length", Int(), regs[args[0]]), None)


def listGet(regs, *args):
    return ReturnValue(Call("list_get", Int(), regs[args[0]], regs[args[1]]), None)


def listAppend(regs, *args):
    # return ReturnValue(None, [(args[0], Expr.Pred("list_append", parseTypeRef(args[0].type), regs[args[1]]))])
    return ReturnValue(
        Call("list_append", parseTypeRef(args[0].type), regs[args[0]], regs[args[1]]),
        None,
    )


def listConcat(regs, *args):
    # return ReturnValue(None, [(args[0], Expr.Pred("list_append", parseTypeRef(args[0].type), regs[args[1]]))])
    return ReturnValue(
        Call("list_concat", parseTypeRef(args[0].type), regs[args[0]], regs[args[1]]),
        None,
    )


fnModels = {
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
    # names for set.h
    "set_create": lambda _: ReturnValue(
        Var("(as emptyset (Set Int))", Set(Int())), None
    ),
    "set_add": lambda regs, *args: ReturnValue(
        Call(
            "insert",
            Set(Int()),
            parseOperand(args[1], regs),
            parseOperand(args[0], regs),
        ),
        None,
    ),
    "set_remove": lambda regs, *args: ReturnValue(
        Call(
            "setminus",
            Set(Int()),
            parseOperand(args[0], regs),
            Call("singleton", Set(Int()), parseOperand(args[1], regs)),
        ),
        None,
    ),
    "set_contains": lambda regs, *args: ReturnValue(
        Ite(
            Call(
                "member",
                Set(Int()),
                parseOperand(args[1], regs),
                parseOperand(args[0], regs),
            ),
            IntLit(1),
            IntLit(0),
        ),
        None,
    ),
}

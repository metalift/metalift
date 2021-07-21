from collections import namedtuple

from ir import Expr, Type, parseTypeRef

ReturnValue = namedtuple("ReturnValue", ["val", "assigns"])

def newlist(regs, *args):
  # return ReturnValue(None, [(args[0], Expr.Pred("list_new", parseTypeRef(args[0].type)))])
  return ReturnValue(Expr.Var("list_empty", Type("MLList", Type.int())), None)


def listLength(regs, *args):
  return ReturnValue(Expr.Pred("list_length", Type.int(), regs[args[0]]), None)

def listGet(regs, *args):
  return ReturnValue(Expr.Pred("list_get", Type.int(), regs[args[0]], regs[args[1]]), None)

def listAppend(regs, *args):
  # return ReturnValue(None, [(args[0], Expr.Pred("list_append", parseTypeRef(args[0].type), regs[args[1]]))])
  return ReturnValue(Expr.Pred("list_append", parseTypeRef(args[0].type), regs[args[0]], regs[args[1]]), None)

fnModels = {
  "_Z7newListv": newlist,
  "_Z10listLengthP4list": listLength,
  "_Z7listGetP4listi": listGet,
  "_Z10listAppendP4listi": listAppend
}

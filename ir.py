from enum import Enum

from llvmlite.binding import ValueRef, TypeRef

import typing
from typing import Any, Callable, Dict, Union


class PrintMode(Enum):
    SMT = 0
    Rosette = 1
    RosetteVC = 2


printMode = PrintMode.SMT

# for external functions to call
def setPrintMode(mode):
    global printMode
    printMode = mode


class Type:
    def __init__(self, name: str, *args: "Type") -> None:
        self.name = name
        self.args = args

    def __repr__(self) -> str:
        if self.name == "Int":
            return "Int"
        elif self.name == "Bool":
            return "Bool"
        elif self.name == "Tuple":
            args = " ".join(str(a) for a in self.args)
            return "(Tuple%d %s)" % (len(self.args), args)
        else:
            return "(%s %s)" % (self.name, " ".join([str(a) for a in self.args]))

    def __eq__(self, other: object) -> bool:
        if isinstance(other, Type):
            if self.name != other.name or len(self.args) != len(other.args):
                return False
            else:
                return all(
                    a1 == a2
                    if isinstance(a1, type) and isinstance(a2, type)
                    else a1.__eq__(a2)
                    for a1, a2 in zip(self.args, other.args)
                )
        return NotImplemented

    def __ne__(self, other: object) -> bool:
        x = self.__eq__(other)
        if x is not NotImplemented:
            return not x
        return NotImplemented

    def __hash__(self) -> int:
        return hash(tuple(sorted({"name": self.name, "args": tuple(self.args)})))


def Int() -> Type:
    return Type("Int")


def Bool() -> Type:
    return Type("Bool")


def Pointer() -> Type:
    return Type("Pointer")


def List(contentT: Type) -> Type:
    return Type("MLList", contentT)


def Fn(retT: Type, *argT: Type) -> Type:
    return Type("Function", retT, *argT)


def Set(contentT: Type) -> Type:
    return Type("Set", contentT)


def Tuple(*elemT: Type) -> Type:
    return Type("Tuple", *elemT)


# first two types are not optional
def Tuple(e1T: Type, e2T: Type, *elemT: Type) -> Type:
    return Type("Tuple", e1T, e2T, *elemT)


class Expr:
    class Kind(Enum):
        Var = "var"
        Lit = "lit"

        Add = "+"
        Sub = "-"
        Mul = "*"

        Eq = "="
        Lt = "<"
        Le = "<="
        Gt = ">"
        Ge = ">="

        And = "and"
        Or = "or"
        Not = "not"

        Implies = "=>"

        Ite = "ite"

        Call = "call"

        Assert = "assert"
        Constraint = "constraint"
        Axiom = "axiom"
        Synth = "synth"
        Choose = "choose"
        FnDecl = "fndecl"
        FnDeclNonRecursive = "fndeclnonrecursive"

        Tuple = "tuple"

    def __init__(self, kind: Kind, type: Type, args: Any) -> None:
        self.kind = kind
        self.args = args
        self.type = type

    def mapArgs(self, f: Callable[["Expr"], "Expr"]) -> "Expr":
        return Expr(self.kind, self.type, [f(a) for a in self.args])

    @staticmethod
    def findCommonExprs(e: "Expr", cnts: Dict["Expr", int]) -> Dict["Expr", int]:
        if e not in cnts:
            cnts[e] = 1
            for i in range(len(e.args)):
                if isinstance(e.args[i], Expr):
                    cnts = Expr.findCommonExprs(e.args[i], cnts)

        else:
            cnts[e] = cnts[e] + 1

        return cnts

    @staticmethod
    def replaceExprs(
        e: Union[bool, "Expr", ValueRef, int, str],
        commonExprs: typing.List[Union["Expr", Any]],
        skipTop: bool = False,
    ) -> Union["Expr", ValueRef]:
        # skipTop is used to ignore the top-level match when simplifying a common expr
        if e not in commonExprs or skipTop:
            if isinstance(e, Expr):
                newArgs = [Expr.replaceExprs(arg, commonExprs) for arg in e.args]
                return Expr(e.kind, e.type, newArgs)
            else:
                return e  # ValueRef or TypeRef
        else:
            assert isinstance(e, Expr)
            if printMode == PrintMode.Rosette or printMode == PrintMode.RosetteVC:
                return Var("(v%d)" % commonExprs.index(e), e.type)
            else:
                return Var("v%d" % commonExprs.index(e), e.type)

    @staticmethod
    def printSynth(e: "Expr") -> str:
        cnts = Expr.findCommonExprs(e.args[1], {})
        commonExprs = list(
            filter(
                lambda k: (cnts[k] > 1 and k.type.name != "Tuple")
                or k.kind == Expr.Kind.Choose,
                cnts.keys(),
            )
        )
        rewritten = Expr.replaceExprs(e.args[1], commonExprs)

        # rewrite common exprs to use each other
        commonExprs = [
            Expr.replaceExprs(e, commonExprs, skipTop=True) for e in commonExprs
        ]

        if printMode == PrintMode.Rosette or printMode == PrintMode.RosetteVC:
            args = " ".join(
                "%s" % (a.name) if isinstance(a, ValueRef) else str(a)
                for a in e.args[2:]
            )

            defs = "[rv (choose %s)]\n" % (
                rewritten
                if rewritten.kind == Expr.Kind.Var or rewritten.kind == Expr.Kind.Lit
                else "%s" % rewritten
            )

            defs = defs + "\n".join(
                "%s %s)]" % ("[v%d (choose" % i, e) for i, e in enumerate(commonExprs)
            )

            return "(define-grammar (%s_gram %s)\n %s\n)" % (e.args[0], args, defs)
        else:  # printMode == PrintMode.SMT
            decls = "((rv %s) %s)" % (
                e.type,
                " ".join(
                    "(%s %s)" % ("v%d" % i, parseTypeRef(e.type))
                    for i, e in enumerate(commonExprs)
                ),
            )
            defs = "(rv %s %s)\n" % (
                e.type,
                rewritten if rewritten.kind == Expr.Kind.Choose else "(%s)" % rewritten,
            )
            defs = defs + "\n".join(
                "(%s %s %s)"
                % (
                    "v%d" % i,
                    parseTypeRef(e.type),
                    e if e.kind == Expr.Kind.Choose else f"({e})",
                )
                for i, e in enumerate(commonExprs)
            )

            body = decls + "\n" + "(" + defs + ")"

            declarations = []
            for a in e.args[2:]:
                if isinstance(a, ValueRef):
                    declarations.append((a.name, parseTypeRef(a.type)))
                else:
                    declarations.append((a.args[0], a.type))

            args = " ".join("(%s %s)" % (d[0], d[1]) for d in declarations)
            return "(synth-fun %s (%s) %s\n%s)" % (e.args[0], args, e.type, body)

    def __repr__(self) -> str:
        global printMode
        listFns = {
            "list_get": "list-ref-noerr",
            "list_append": "list-append",
            "list_empty": "list-empty",
            "list_tail": "list-tail-noerr",
            "list_length": "length",
            "list_take": "list-take-noerr",
            "list_prepend": "list-prepend",
            "list_eq": "equal?",
            "list_concat": "list-concat",
        }
        kind = self.kind
        if kind == Expr.Kind.Var or kind == Expr.Kind.Lit:
            if kind == Expr.Kind.Lit and self.type == Bool():
                if self.args[0] == True:
                    return "true"
                else:
                    return "false"
            else:
                return str(self.args[0])
        elif kind == Expr.Kind.Call or kind == Expr.Kind.Choose:
            if printMode == PrintMode.SMT:
                noParens = kind == Expr.Kind.Call and len(self.args) == 1
                return (
                    ("" if noParens else "(")
                    + " ".join(
                        [
                            a.name
                            if isinstance(a, ValueRef) and a.name != ""
                            else str(a)
                            for a in self.args
                        ]
                    )
                    + ("" if noParens else ")")
                )
            else:
                if isinstance(self.args[0], str):
                    if (
                        self.args[0].startswith("inv") or self.args[0].startswith("ps")
                    ) and printMode == PrintMode.RosetteVC:
                        callStr = "( " + "%s " % (str(self.args[0]))
                        for a in self.args[1:]:
                            callStr += str(a) + " "
                        callStr += ")"
                        return callStr
                    elif (
                        self.args[0].startswith("list")
                        and printMode == PrintMode.RosetteVC
                    ):
                        callStr = (
                            "("
                            + "%s"
                            % (
                                listFns[self.args[0]]
                                if self.args[0] in listFns.keys()
                                else self.args[0]
                            )
                            + " "
                        )
                        for a in self.args[1:]:
                            if isinstance(a, ValueRef) and a.name != "":
                                callStr += "%s " % (a.name)
                            else:
                                callStr += str(a) + " "
                        callStr += ")"
                        return callStr

                    elif (
                        self.type.name == "Function" and printMode == PrintMode.Rosette
                    ):
                        return "%s" % (self.args[0])
                    else:
                        noParens = len(self.args) == 1
                        return (
                            ("" if noParens else "(")
                            + " ".join(
                                [
                                    a.name
                                    if isinstance(a, ValueRef) and a.name != ""
                                    else str(a)
                                    for a in self.args
                                ]
                            )
                            + ("" if noParens else ")")
                        )
                else:
                    return " ".join(
                        [
                            a.name
                            if isinstance(a, ValueRef) and a.name != ""
                            else str(a)
                            for a in self.args
                        ]
                    )

        elif kind == Expr.Kind.Synth:
            return Expr.printSynth(self)

        elif kind == Expr.Kind.Axiom:
            if printMode == PrintMode.SMT:
                vs = ["(%s %s)" % (a.args[0], a.type) for a in self.args[1:]]
                return "(assert (forall ( %s ) ) %s) " % (" ".join(vs), self.args[0])
            else:
                raise Exception("NYI: %s" % self)

        elif kind == Expr.Kind.FnDecl or kind == Expr.Kind.FnDeclNonRecursive:
            if printMode == PrintMode.SMT:
                declarations = []
                for a in self.args[2:]:
                    if isinstance(a, ValueRef):
                        declarations.append((a.name, parseTypeRef(a.type)))
                    else:
                        declarations.append((a.args[0], a.type))

                args = " ".join("(%s %s)" % (d[0], d[1]) for d in declarations)

                def_str = "define-fun-rec" if kind == Expr.Kind.FnDecl else "define-fun"

                return "(%s %s (%s) %s\n%s)" % (
                    def_str,
                    self.args[0],
                    args,
                    self.type if self.type.name != "Function" else self.type.args[0],
                    self.args[1],
                )
            else:
                args = " ".join(
                    [
                        "%s" % (a.name)
                        if isinstance(a, ValueRef) and a.name != ""
                        else "%s" % (a.args[0])
                        for a in self.args[2:]
                    ]
                )

                def_str = (
                    "define"
                    if kind == Expr.Kind.FnDeclNonRecursive
                    else "define-bounded"
                )

                return "(%s (%s %s) \n%s)" % (
                    def_str,
                    self.args[0],
                    args,
                    self.args[1],
                )
        elif kind == Expr.Kind.Tuple:
            if printMode == PrintMode.RosetteVC:
                # original code was "(make-tuple %s) % " ".join(["%s" % str(arg) for arg in self.args])
                # but arg can be a ValueRef and calling str on it will return both type and name e.g., i32 %arg
                return str(Call("make-tuple", self.type, *self.args))
            else:
                args = " ".join(["%s" % arg for arg in self.args])
                return "(tuple2 %s)" % args

        # elif kind == Expr.Kind.Eq and self.args[0].type.name == "Tuple":
        #     return repr(
        #         And(
        #             *[
        #                 Eq(TupleSel(self.args[0], i), TupleSel(self.args[1], i))
        #                 for i in range(len(self.args[0].type.args))
        #             ]
        #         )
        #     )
        else:
            if printMode == PrintMode.SMT:
                value = self.kind.value
            elif printMode == PrintMode.RosetteVC:
                k = self.kind
                if k == Expr.Kind.And:
                    value = "&&"
                elif k == Expr.Kind.Eq:
                    value = "equal?"
                elif k == Expr.Kind.Ite:
                    value = "if"
                else:
                    value = self.kind.value
            else:
                k = self.kind
                if k == Expr.Kind.And:
                    value = "_and"
                elif k == Expr.Kind.Eq:
                    value = "_eq"
                elif k == Expr.Kind.Or:
                    value = "_or"
                elif k == Expr.Kind.Implies:
                    value = "_implies"
                elif k == Expr.Kind.Not:
                    value = "_not"
                elif k == Expr.Kind.Ite:
                    value = "_if"
                elif k == Expr.Kind.Add:
                    value = "_add"
                elif k == Expr.Kind.Sub:
                    value = "_sub"
                elif k == Expr.Kind.Mul:
                    value = "_mul"
                elif k == Expr.Kind.Le:
                    value = "_lte"
                elif k == Expr.Kind.Lt:
                    value = "_lt"
                elif k == Expr.Kind.Ge:
                    value = "_gte"
                elif k == Expr.Kind.Gt:
                    value = "_gt"

                else:
                    value = self.kind.value

            if printMode == PrintMode.SMT or printMode == PrintMode.Rosette:
                return (
                    "("
                    + value
                    + " "
                    + " ".join(
                        [
                            a.name
                            if isinstance(a, ValueRef) and a.name != ""
                            else str(a)
                            for a in self.args
                        ]
                    )
                    + ")"
                )
            else:
                retStr = "(" + value + " "
                for a in self.args:
                    if isinstance(a, ValueRef) and a.name != "":
                        retStr += "%s" % (a.name) + " "
                    else:
                        strExp = str(a)
                        if (strExp) in listFns.keys() and "list_empty" in (strExp):
                            retStr += "(" + listFns[strExp] + ")" + " "
                        elif (strExp) in listFns.keys():
                            retStr += listFns[strExp]
                        else:
                            retStr += strExp + " "
                retStr += ")"
                return retStr

    # commented out so that common exprs can be detected
    #
    # def __eq__(self, other):
    #   if isinstance(other, Expr):
    #     if self.kind != other.kind or len(self.args) != len(other.args):
    #       return False
    #     else:
    #       return all( a1 == a2 if isinstance(a1, type) and isinstance(a2, type) else a1.__eq__(a2)
    #                   for a1,a2 in zip(self.args, other.args))
    #   return NotImplemented
    #
    # def __ne__(self, other):
    #   x = self.__eq__(other)
    #   if x is not NotImplemented:
    #     return not x
    #   return NotImplemented

    def __hash__(self) -> int:
        return hash(
            tuple(
                sorted({"kind": self.kind, "type": self.type, "args": tuple(self.args)})
            )
        )


def Var(name: str, ty: Type) -> Expr:
    return Expr(Expr.Kind.Var, ty, [name])


def Lit(val: Union[bool, int], ty: Type) -> Expr:
    return Expr(Expr.Kind.Lit, ty, [val])


def IntLit(val: int) -> Expr:
    return Lit(val, Int())


def BoolLit(val: bool) -> Expr:
    return Lit(val, Bool())


def Add(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Add, Int(), args)


def Sub(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Sub, Int(), args)


def Mul(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Mul, Int(), args)


def Eq(e1: Expr, e2: Expr) -> Expr:
    return Expr(Expr.Kind.Eq, Bool(), [e1, e2])


def Lt(e1: Expr, e2: Expr) -> Expr:
    return Expr(Expr.Kind.Lt, Bool(), [e1, e2])


def Le(e1: Expr, e2: Expr) -> Expr:
    return Expr(Expr.Kind.Le, Bool(), [e1, e2])


def Gt(e1: Expr, e2: Expr) -> Expr:
    return Expr(Expr.Kind.Gt, Bool(), [e1, e2])


def Ge(e1: Expr, e2: Expr) -> Expr:
    return Expr(Expr.Kind.Ge, Bool(), [e1, e2])


def And(*args: Expr) -> Expr:
    return Expr(Expr.Kind.And, Bool(), args)


def Or(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Or, Bool(), args)


def Not(e: Expr) -> Expr:
    return Expr(Expr.Kind.Not, Bool(), [e])


def Implies(e1: Union[Expr, "MLInst"], e2: Union[Expr, "MLInst"]) -> Expr:
    return Expr(Expr.Kind.Implies, Bool(), [e1, e2])


def Ite(c: Expr, e1: Expr, e2: Expr) -> Expr:
    return Expr(Expr.Kind.Ite, e1.type, [c, e1, e2])


def Call(name: str, returnT: Type, *args: Expr) -> Expr:
    return Expr(Expr.Kind.Call, returnT, [name, *args])


def Assert(e: Expr) -> Expr:
    return Expr(Expr.Kind.Assert, Bool(), [e])


def Constraint(e: Expr) -> Expr:
    return Expr(Expr.Kind.Constraint, Bool(), [e])


def MakeTuple(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Tuple, Tuple(*[a.type for a in args]), args)


# tuple accessors
def First(t: Expr) -> Expr:
    return Call("first", Int(), t)


def Second(t: Expr) -> Expr:
    return Call("second", Int(), t)


def Third(t: Expr) -> Expr:
    return Call("third", Int(), t)


def Fourth(t: Expr) -> Expr:
    return Call("fourth", Int(), t)


def Axiom(e: Expr, *vars: Expr) -> Expr:
    return Expr(Expr.Kind.Axiom, Bool(), [e, *vars])


# the body of a synth-fun
def Synth(name: str, body: Expr, *args: Expr) -> Expr:
    return Expr(Expr.Kind.Synth, body.type, [name, body, *args])


def Choose(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Choose, args[0].type, args)


def FnDecl(name: str, returnT: Type, body: Union[Expr, str], *args: Expr) -> Expr:
    return Expr(Expr.Kind.FnDecl, returnT, [name, body, *args])


def FnDeclNonRecursive(
    name: str, returnT: Type, body: Union[Expr, str], *args: Expr
) -> Expr:
    return Expr(Expr.Kind.FnDeclNonRecursive, returnT, [name, body, *args])


# class to represent the extra instructions that are inserted into the llvm code during analysis
class MLInst:
    class Kind:  # not defined as an enum as computeVC switches on the opcode str
        Assert = "assert"
        Assume = "assume"
        Call = "call"
        Eq = "eq"
        Havoc = "havoc"
        Load = "load"
        Not = "not"
        Or = "or"
        Return = "return"

    def __init__(self, opcode: str, *operands: Union["MLInst", Expr, ValueRef]) -> None:
        self.opcode = opcode
        self.operands = operands

    def __str__(self) -> str:
        if self.opcode == MLInst.Kind.Call:
            return "call %s %s(%s)" % (
                self.operands[0],
                self.operands[1],
                " ".join(
                    [
                        o.name if isinstance(o, ValueRef) else str(o)
                        for o in self.operands[2:]
                    ]
                ),
            )
        else:
            return "(%s %s)" % (
                self.opcode,
                " ".join(
                    [
                        o.name if isinstance(o, ValueRef) else str(o)
                        for o in self.operands
                    ]
                ),
            )


def MLInst_Assert(val: Union[MLInst, Expr, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Assert, val)


def MLInst_Assume(val: Union[MLInst, Expr, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Assume, val)


def MLInst_Call(name: str, retType: Type, *args: Union[MLInst, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Call, name, retType, *args)


def MLInst_Eq(
    v1: Union[MLInst, Expr, ValueRef], v2: Union[MLInst, Expr, ValueRef]
) -> MLInst:
    return MLInst(MLInst.Kind.Eq, v1, v2)


def MLInst_Havoc(*args: Union[MLInst, Expr, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Havoc, *args)


def MLInst_Load(val: Union[MLInst, Expr, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Load, val)


def MLInst_Not(val: Union[MLInst, Expr, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Not, val)


def MLInst_Or(val: Union[MLInst, Expr, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Or, val)


def MLInst_Return(val: Union[MLInst, Expr, ValueRef]) -> MLInst:
    return MLInst(MLInst.Kind.Return, val)


def parseTypeRef(t: Union[Type, TypeRef]) -> Type:
    # ty.name returns empty string. possibly bug
    if isinstance(t, Type):
        return t

    tyStr = str(t)

    if tyStr == "i64":
        return Int()
    elif tyStr == "i32" or tyStr == "i32*" or tyStr == "Int":
        return Int()
    elif tyStr == "i1" or tyStr == "Bool":
        return Bool()
    elif (
        tyStr == "%struct.list*" or tyStr == "%struct.list**" or tyStr == "(MLList Int)"
    ):
        return Type("MLList", Int())
    elif tyStr.startswith("%struct.set"):
        return Set(Int())
    elif tyStr == "(Function Bool)":
        return Type("Function", Bool())
    elif tyStr == "(Function Int)":
        return Type("Function", Int())
    elif tyStr.startswith("%struct.tup"):
        # ToDo FIX return type for multiple values
        return Tuple(Int(), Int())
    else:
        raise Exception("NYI %s" % t)

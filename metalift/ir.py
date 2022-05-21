from enum import Enum
import enum

from llvmlite.binding import ValueRef, TypeRef, common
from collections import Counter
import typing
from typing import Any, Callable, Dict, Union


class PrintMode(Enum):
    SMT = 0
    Rosette = 1


class CVC5UnsupportedException(Exception):
    pass


class Type:
    def __init__(self, name: str, *args: "Type") -> None:
        self.name = name
        self.args = args

    def toSMT(self) -> str:
        if (
            self.name == "Int"
            or self.name == "ClockInt"
            or self.name == "BoolInt"
            or self.name == "OpaqueInt"
            or self.name == "NodeIDInt"
        ):
            return "Int"
        elif self.name == "Bool":
            return "Bool"
        elif self.name == "String":
            return "String"
        elif self.name == "Tuple":
            args = " ".join(a.toSMT() for a in self.args)
            return "(Tuple%d %s)" % (len(self.args), args)
        elif self.name == "Map":
            raise CVC5UnsupportedException("Map")
        else:
            return "(%s %s)" % (
                self.name,
                " ".join(
                    [a.toSMT() if isinstance(a, Type) else str(a) for a in self.args]
                ),
            )

    def __repr__(self) -> str:
        if len(self.args) == 0:
            return self.name
        else:
            return "(%s %s)" % (self.name, " ".join([str(a) for a in self.args]))

    def erase(self) -> "Type":
        if (
            self.name == "ClockInt"
            or self.name == "BoolInt"
            or self.name == "OpaqueInt"
            or self.name == "NodeIDInt"
        ):
            return Int()
        else:
            return Type(
                self.name, *[a.erase() if isinstance(a, Type) else a for a in self.args]
            )

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


def ClockInt() -> Type:
    return Type("ClockInt")


def BoolInt() -> Type:
    return Type("BoolInt")


def OpaqueInt() -> Type:
    return Type("OpaqueInt")


def NodeIDInt() -> Type:
    return Type("NodeIDInt")


def Bool() -> Type:
    return Type("Bool")


# for string literals
def String() -> Type:
    return Type("String")


def Pointer(t: Type) -> Type:
    return Type("Pointer", t)


def List(contentT: Type) -> Type:
    return Type("MLList", contentT)


def Fn(retT: Type, *argT: Type) -> Type:
    return Type("Function", retT, *argT)


def Set(contentT: Type) -> Type:
    return Type("Set", contentT)


def Map(keyT: Type, valT: Type) -> Type:
    return Type("Map", keyT, valT)


# first type is not optional
def TupleT(e1T: Type, *elemT: Type) -> Type:
    return Type("Tuple", e1T, *elemT)


class Expr:
    # class Kind(Enum):
    #     Var = "var"
    #     Lit = "lit"
    #     Object = "obj"
    #
    #     Add = "+"
    #     Sub = "-"
    #     Mul = "*"
    #
    #     Eq = "="
    #     Lt = "<"
    #     Le = "<="
    #     Gt = ">"
    #     Ge = ">="
    #
    #     And = "and"
    #     Or = "or"
    #     Not = "not"
    #
    #     Implies = "=>"
    #
    #     Ite = "ite"
    #     Let = "let"
    #
    #     Call = "call"
    #     CallValue = "callvalue"
    #
    #     Assert = "assert"
    #     Constraint = "constraint"
    #     Axiom = "axiom"
    #     Synth = "synth"
    #     Choose = "choose"
    #     FnDecl = "fndecl"
    #     FnDeclNonRecursive = "fndeclnonrecursive"
    #     FnDefine = "fndefine"
    #     Lambda = "lambda"
    #
    #     Tuple = "tuple"
    #     TupleGet = "tupleGet"

    # def __init__(self, kind: Kind, type: Type, args: Any) -> None:
    #     self.kind = kind
    #     self.args = args
    #     self.type = type

    def __init__(self, type: Type, args: Any) -> None:
        self.args = args
        self.type = type

    # XXX
    def mapArgs(self, f: Callable[["Expr"], "Expr"]) -> "Expr":
        # return Expr(self.type, [f(a) for a in self.args])
        if isinstance(self, Var):
            return Var(typing.cast(str, f(self.args[0])), self.type)
        elif isinstance(self, Lit):
            return Lit(typing.cast(Union[bool, int, str], f(self.args[0])), self.type)
        elif isinstance(self, Add):
            return Add(*[f(a) for a in self.args])
        elif isinstance(self, Sub):
            return Sub(*[f(a) for a in self.args])
        elif isinstance(self, Mul):
            return Mul(*[f(a) for a in self.args])
        elif isinstance(self, Implies):
            return Implies(*[f(a) for a in self.args])
        elif isinstance(self, And):
            return And(*[f(a) for a in self.args])
        elif isinstance(self, Or):
            return Or(*[f(a) for a in self.args])
        elif isinstance(self, Not):
            return Not(*[f(a) for a in self.args])
        elif isinstance(self, Eq):
            return Eq(*[f(a) for a in self.args])
        elif isinstance(self, Ge):
            return Ge(*[f(a) for a in self.args])
        elif isinstance(self, Gt):
            return Gt(*[f(a) for a in self.args])
        elif isinstance(self, Le):
            return Le(*[f(a) for a in self.args])
        elif isinstance(self, Lt):
            return Lt(*[f(a) for a in self.args])
        elif isinstance(self, Ite):
            return Ite(*[f(a) for a in self.args])
        elif isinstance(self, Tuple):
            return Tuple(*[f(a) for a in self.args])
        elif isinstance(self, Let):
            return Let(*[f(a) for a in self.args])
        elif isinstance(self, TupleGet):
            return TupleGet(f(self.args[0]), *[f(a) for a in self.args[1:]])
        elif isinstance(self, Call):
            return Call(
                typing.cast(str, f(self.args[0])),
                self.type,
                *[f(a) for a in self.args[1:]],
            )
        elif isinstance(self, CallValue):
            return CallValue(f(self.args[0]), *[f(a) for a in self.args[1:]])
        else:
            raise Exception("NYI: %s" % self)

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
        mode: PrintMode,
        skipTop: bool = False,
    ) -> Union["Expr", ValueRef]:
        # skipTop is used to ignore the top-level match when simplifying a common expr
        if e not in commonExprs or skipTop:
            if isinstance(e, Expr):
                newArgs = [Expr.replaceExprs(arg, commonExprs, mode) for arg in e.args]
                if isinstance(e, Var):
                    return Var(typing.cast(str, newArgs[0]), e.type)
                elif isinstance(e, Lit):
                    return Lit(typing.cast(Union[bool, int, str], newArgs[0]), e.type)
                elif isinstance(e, Ge):
                    return Ge(*newArgs)
                elif isinstance(e, Gt):
                    return Gt(*newArgs)
                elif isinstance(e, Le):
                    return Le(*newArgs)
                elif isinstance(e, Lt):
                    return Lt(*newArgs)
                elif isinstance(e, Eq):
                    return Eq(*newArgs)
                elif isinstance(e, Ite):
                    return Ite(*newArgs)
                elif isinstance(e, And):
                    return And(*newArgs)
                elif isinstance(e, Or):
                    return Or(*newArgs)
                elif isinstance(e, Not):
                    return Not(*newArgs)
                elif isinstance(e, Add):
                    return Add(*newArgs)
                elif isinstance(e, Sub):
                    return Sub(*newArgs)
                elif isinstance(e, Mul):
                    return Mul(*newArgs)
                elif isinstance(e, Call):
                    return Call(typing.cast(str, newArgs[0]), e.type, *newArgs[1:])
                elif isinstance(e, Choose):
                    return Choose(*newArgs)
                elif isinstance(e, Tuple):
                    return Tuple(*newArgs)
                elif isinstance(e, TupleGet):
                    return TupleGet(*newArgs)
                elif isinstance(e, Let):
                    return Let(*newArgs)
                else:
                    raise Exception("NYI: %s" % e)
                # XXX
                # return Expr(e.type, newArgs)
            else:
                return e  # ValueRef or TypeRef
        else:
            assert isinstance(e, Expr)
            if mode == PrintMode.Rosette:
                return Var("(v%d)" % commonExprs.index(e), e.type)
            else:
                return Var("v%d" % commonExprs.index(e), e.type)

    # def __repr__(self) -> str:
    #     if isinstance(self, Var):
    #         return self.args[0]  # type: ignore
    #     elif isinstance(self, Call):
    #         return "(%s:%s %s)" % (
    #             self.args[0],
    #             self.type,
    #             " ".join(str(a) for a in self.args[1:]),
    #         )
    #     else:
    #         return "(%s:%s %s)" % (
    #             type(self).__name__,
    #             self.type,
    #             " ".join(str(a) for a in self.args),
    #         )

    def __repr__(self) -> str:
        return "(%s:%s %s)" % (
            type(self).__name__,
            self.type,
            " ".join(str(a) for a in self.args),
        )

    # commented out so that common exprs can be detected
    #
    def __eq__(self, other: Any) -> bool:
        if isinstance(other, Expr):
            if (
                type(self) != type(other)
                or parseTypeRef(self.type).erase() != parseTypeRef(other.type).erase()
                or len(self.args) != len(other.args)
            ):
                return False
            else:
                return all(
                    a1 == a2
                    if isinstance(a1, Type) and isinstance(a2, Type)
                    else a1.__eq__(a2)
                    for a1, a2 in zip(self.args, other.args)
                )
        return NotImplemented

    #
    # def __ne__(self, other):
    #   x = self.__eq__(other)
    #   if x is not NotImplemented:
    #     return not x
    #   return NotImplemented

    def __hash__(self) -> int:
        return hash(tuple(sorted({"type": self.type, "args": tuple(self.args)})))

    # def toSMT(self) -> str:
    #     if isinstance(self, Var) or isinstance(self, Lit):
    #         if isinstance(self, Lit) and self.type == Bool():
    #             if self.args[0] == True:
    #                 return "true"
    #             else:
    #                 return "false"
    #         else:
    #             return str(self.args[0])
    #
    #     elif (
    #         isinstance(self, Call)
    #         or isinstance(self, CallValue)
    #         or isinstance(self, Choose)
    #     ):
    #         noParens = isinstance(self, Call) and len(self.args) == 1
    #         retVal = []
    #
    #         if self.args[0] == "set-create":
    #             return f"(as set.empty {self.type.toSMT()})"
    #
    #         if self.args[0] == "tupleGet":
    #             argvals = self.args[:-1]
    #         else:
    #             argvals = self.args
    #
    #         for idx, a in enumerate(argvals):
    #             if isinstance(a, ValueRef) and a.name != "":
    #                 retVal.append(a.name)
    #             elif (str(a)) == "make-tuple":
    #                 retVal.append("tuple%d" % (len(self.args[idx + 1 :])))
    #             elif (str(a)) == "tupleGet":
    #                 if self.args[idx + 1].args[0] == "make-tuple":
    #                     retVal.append(
    #                         "tuple%d_get%d"
    #                         % (
    #                             len(self.args[idx + 1].args) - 1,
    #                             self.args[idx + 2].args[0],
    #                         )
    #                     )
    #                 else:
    #                     # HACK: if function argument is a tuple, count I's in the mangled names of args to get number of elements in tuple
    #                     freq: typing.Counter[str] = Counter(
    #                         self.args[idx + 1].args[0].split("_")[1]
    #                     )
    #                     retVal.append(
    #                         "tuple%d_get%d" % (freq["i"], self.args[idx + 2].args[0])
    #                     )
    #             elif (str(a)).startswith("set-"):
    #                 retVal.append("set.%s" % (str(a)[4:]))
    #             elif (str(a)).startswith("map-"):
    #                 retVal.append("map_%s" % (str(a)[4:]))
    #             elif isinstance(a, str):
    #                 retVal.append(str(a))
    #             else:
    #                 retVal.append(a.toSMT())
    #
    #         retT = (
    #             ("" if noParens else "(") + " ".join(retVal) + ("" if noParens else ")")
    #         )
    #
    #         return retT
    #
    #     elif isinstance(self, Synth):
    #         cnts = Expr.findCommonExprs(self.args[1], {})
    #         commonExprs = list(
    #             filter(
    #                 lambda k: isinstance(k, Choose),
    #                 cnts.keys(),
    #             )
    #         )
    #         rewritten = Expr.replaceExprs(self.args[1], commonExprs, PrintMode.SMT)
    #
    #         # rewrite common exprs to use each other
    #         commonExprs = [
    #             Expr.replaceExprs(e, commonExprs, PrintMode.SMT, skipTop=True)
    #             for e in commonExprs
    #         ]
    #
    #         decls = "((rv %s) %s)" % (
    #             self.type.toSMT(),
    #             " ".join(
    #                 "(%s %s)" % ("v%d" % i, parseTypeRef(e.type).toSMT())
    #                 for i, e in enumerate(commonExprs)
    #             ),
    #         )
    #         defs = "(rv %s %s)\n" % (
    #             self.type.toSMT(),
    #             rewritten.toSMT()
    #             if isinstance(rewritten, Choose)
    #             else "(%s)" % rewritten.toSMT(),
    #         )
    #         defs = defs + "\n".join(
    #             "(%s %s %s)"
    #             % (
    #                 "v%d" % i,
    #                 parseTypeRef(e.type).toSMT(),
    #                 e.toSMT() if isinstance(self, Choose) else f"({e.toSMT()})",
    #             )
    #             for i, e in enumerate(commonExprs)
    #         )
    #
    #         body = decls + "\n" + "(" + defs + ")"
    #
    #         declarations = []
    #         for a in self.args[2:]:
    #             if isinstance(a, ValueRef):
    #                 declarations.append((a.name, parseTypeRef(a.type)))
    #             else:
    #                 declarations.append((a.args[0], a.type))
    #
    #         args = " ".join("(%s %s)" % (d[0], d[1].toSMT()) for d in declarations)
    #         return "(synth-fun %s (%s) %s\n%s)" % (
    #             self.args[0],
    #             args,
    #             self.type.toSMT(),
    #             body,
    #         )
    #
    #     elif isinstance(self, Axiom):
    #         vs = ["(%s %s)" % (a.args[0], a.type) for a in self.args[1:]]
    #         return "(assert (forall ( %s ) %s ))" % (" ".join(vs), self.args[0].toSMT())
    #     elif isinstance(self, Lambda):
    #         # TODO(shadaj): extract during filtering assuming no captures
    #         raise Exception("Lambda not supported")
    #     elif (
    #         isinstance(self, FnDecl)
    #         or isinstance(self, FnDeclNonRecursive)
    #         or isinstance(self, FnDefine)
    #     ):
    #         if (
    #             isinstance(self, FnDefine) or self.args[1] is None
    #         ):  # uninterpreted function
    #             args_type = " ".join(
    #                 parseTypeRef(a.type).toSMT() for a in self.args[2:]
    #             )
    #             return "(declare-fun %s (%s) %s)" % (
    #                 self.args[0],
    #                 args_type,
    #                 parseTypeRef(self.type),
    #             )
    #
    #         else:
    #             declarations = []
    #             for a in self.args[2:]:
    #                 if isinstance(a, ValueRef):
    #                     declarations.append((a.name, parseTypeRef(a.type)))
    #                 else:
    #                     declarations.append((a.args[0], a.type))
    #
    #             args = " ".join("(%s %s)" % (d[0], d[1].toSMT()) for d in declarations)
    #
    #             def_str = "define-fun-rec" if isinstance(self, FnDecl) else "define-fun"
    #
    #             return "(%s %s (%s) %s\n%s)" % (
    #                 def_str,
    #                 self.args[0],
    #                 args,
    #                 (
    #                     self.type if self.type.name != "Function" else self.type.args[0]
    #                 ).toSMT(),
    #                 self.args[1]
    #                 if isinstance(self.args[1], str)
    #                 else self.args[1].toSMT(),
    #             )
    #
    #     elif isinstance(self, Tuple):
    #         args = " ".join(
    #             [
    #                 arg.name if isinstance(arg, ValueRef) else arg.toSMT()
    #                 for arg in self.args
    #             ]
    #         )
    #         return "(tuple%d %s)" % (len(self.args), args)
    #
    #     elif isinstance(self, TupleGet):
    #         # example: generate (tuple2_get0 t)
    #         return "(tuple%d_get%d %s)" % (
    #             len(self.args[0].type.args),
    #             self.args[1].args[0],
    #             self.args[0].toSMT(),
    #         )  # args[1] must be an int literal
    #     elif isinstance(self, Let):
    #         return "(let ((%s %s)) %s)" % (
    #             self.args[0].toSMT(),
    #             self.args[1].toSMT(),
    #             self.args[2].toSMT(),
    #         )
    #     else:
    #         value = self.SMTName
    #         return (
    #             "("
    #             + value
    #             + " "
    #             + " ".join(
    #                 [
    #                     a.name
    #                     if isinstance(a, ValueRef) and a.name != ""
    #                     else a.toSMT()
    #                     if isinstance(a, Expr)
    #                     else str(a)
    #                     for a in self.args
    #                 ]
    #             )
    #             + ")"
    #         )

    def toSMT(self) -> str:
        raise NotImplementedError

    @staticmethod
    def toSMTSimple(e: "Expr", name: str) -> str:
        value = name
        return (
            "("
            + value
            + " "
            + " ".join(
                [
                    a.name
                    if isinstance(a, ValueRef) and a.name != ""
                    else a.toSMT()
                    if isinstance(a, Expr)
                    else str(a)
                    for a in e.args
                ]
            )
            + ")"
        )

    # def toRosette(
    #     self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    # ) -> str:
    #     listFns = {
    #         "list_get": "list-ref-noerr",
    #         "list_append": "list-append",
    #         "list_empty": "list-empty",
    #         "list_tail": "list-tail-noerr",
    #         "list_length": "length",
    #         "list_take": "list-take-noerr",
    #         "list_prepend": "list-prepend",
    #         "list_eq": "equal?",
    #         "list_concat": "list-concat",
    #     }
    #     if isinstance(self, Var) or isinstance(self, Lit):
    #         if isinstance(self, Lit) and self.type == Bool():
    #             if self.args[0] == True:
    #                 return "true"
    #             else:
    #                 return "false"
    #         else:
    #             return str(self.args[0])
    #
    #     elif (
    #         isinstance(self, Call)
    #         or isinstance(self, CallValue)
    #         or isinstance(self, Choose)
    #     ):
    #         if isinstance(self.args[0], str) or isinstance(self, CallValue):
    #             if isinstance(self.args[0], str) and (
    #                 self.args[0].startswith("inv") or self.args[0].startswith("ps")
    #             ):
    #                 callStr = "( " + "%s " % (str(self.args[0]))
    #                 for a in self.args[1:]:
    #                     callStr += a.toRosette() + " "
    #                 callStr += ")"
    #                 return callStr
    #             elif isinstance(self.args[0], str) and self.args[0].startswith("list"):
    #                 callStr = (
    #                     "("
    #                     + "%s"
    #                     % (
    #                         listFns[self.args[0]]
    #                         if self.args[0] in listFns.keys()
    #                         else self.args[0]
    #                     )
    #                     + " "
    #                 )
    #                 for a in self.args[1:]:
    #                     if isinstance(a, ValueRef) and a.name != "":
    #                         callStr += "%s " % (a.name)
    #                     else:
    #                         callStr += a.toRosette() + " "
    #                 callStr += ")"
    #                 return callStr
    #             else:
    #                 return (
    #                     "("
    #                     + " ".join(
    #                         [
    #                             a.name
    #                             if isinstance(a, ValueRef) and a.name != ""
    #                             else a
    #                             if isinstance(a, str)
    #                             else a.toRosette()
    #                             for a in self.args
    #                         ]
    #                     )
    #                     + ")"
    #                 )
    #         else:
    #             return " ".join(
    #                 [
    #                     a.name
    #                     if isinstance(a, ValueRef) and a.name != ""
    #                     else str(a)
    #                     if isinstance(a, str)
    #                     else a.toRosette()
    #                     for a in self.args
    #                 ]
    #             )
    #
    #     elif isinstance(self, Synth):
    #         cnts = Expr.findCommonExprs(self.args[1], {})
    #         commonExprs = list(
    #             filter(
    #                 lambda k: isinstance(k, Choose),
    #                 cnts.keys(),
    #             )
    #         )
    #         rewritten = Expr.replaceExprs(self.args[1], commonExprs, PrintMode.Rosette)
    #
    #         # rewrite common exprs to use each other
    #         commonExprs = [
    #             Expr.replaceExprs(e, commonExprs, PrintMode.Rosette, skipTop=True)
    #             for e in commonExprs
    #         ]
    #
    #         args = " ".join(
    #             "%s" % a.name
    #             if isinstance(a, ValueRef)
    #             else str(a)
    #             if isinstance(a, str)
    #             else a.toRosette()
    #             for a in self.args[2:]
    #         )
    #
    #         defs = "[rv (choose %s)]\n" % rewritten.toRosette()
    #
    #         if writeChoicesTo != None:
    #             for i, e in enumerate(commonExprs):
    #                 writeChoicesTo[f"v{i}"] = e  # type: ignore
    #
    #         defs = defs + "\n".join(
    #             "%s %s)]" % ("[v%d (choose" % i, e.toRosette())
    #             for i, e in enumerate(commonExprs)
    #         )
    #
    #         return "(define-grammar (%s_gram %s)\n %s\n)" % (self.args[0], args, defs)
    #
    #     elif isinstance(self, Axiom):
    #         return ""  # axioms are only for verification
    #     elif isinstance(self, Lambda):
    #         args = " ".join(
    #             [
    #                 "%s" % (a.name)
    #                 if isinstance(a, ValueRef) and a.name != ""
    #                 else "%s" % (a.args[0])
    #                 for a in self.args[1:]
    #             ]
    #         )
    #
    #         return "(lambda (%s) %s)" % (
    #             args,
    #             self.args[0].toRosette(),
    #         )
    #     elif isinstance(self, FnDecl) or isinstance(self, FnDeclNonRecursive):
    #         if self.args[1] is None:  # uninterpreted function
    #             args_type = " ".join(
    #                 ["%s" % toRosetteType(a.type) for a in self.args[2:]]
    #             )
    #             return "(define-symbolic %s (~> %s %s))" % (
    #                 self.args[0],
    #                 args_type,
    #                 toRosetteType(self.type),
    #             )
    #
    #         else:
    #             args = " ".join(
    #                 [
    #                     "%s" % (a.name)
    #                     if isinstance(a, ValueRef) and a.name != ""
    #                     else "%s" % (a.args[0])
    #                     for a in self.args[2:]
    #                 ]
    #             )
    #
    #             def_str = (
    #                 "define"
    #                 if isinstance(self, FnDeclNonRecursive)
    #                 else "define-bounded"
    #             )
    #
    #             return "(%s (%s %s) \n%s)" % (
    #                 def_str,
    #                 self.args[0],
    #                 args,
    #                 self.args[1].toRosette(),
    #             )
    #     elif isinstance(self, FnDefine):
    #         return ""  # only for verification
    #     elif isinstance(self, Tuple):
    #         # original code was "(make-tuple %s) % " ".join(["%s" % str(arg) for arg in self.args])
    #         # but arg can be a ValueRef and calling str on it will return both type and name e.g., i32 %arg
    #         return Call("make-tuple", self.type, *self.args).toRosette()
    #
    #     elif isinstance(self, TupleGet):
    #         return "(tupleGet %s)" % " ".join(
    #             ["%s" % arg.toRosette() for arg in self.args]
    #         )
    #     elif isinstance(self, Let):
    #         return f"(let ([{self.args[0].toRosette()} {self.args[1].toRosette() if isinstance(self.args[1], Expr) else str(self.args[1])}]) {self.args[2].toRosette()})"
    #     else:
    #         if isinstance(self, And):
    #             value = "&&"
    #         elif isinstance(self, Eq):
    #             if self.args[0].type.name == "Set":
    #                 value = "set-eq"
    #             else:
    #                 value = "equal?"
    #         elif isinstance(self, Ite):
    #             value = "if"
    #         else:
    #             value = self.RosetteName
    #
    #         retStr = "(" + value + " "
    #         for a in self.args:
    #             if isinstance(a, ValueRef) and a.name != "":
    #                 retStr += "%s" % (a.name) + " "
    #             else:
    #                 strExp = a.toRosette() if isinstance(a, Expr) else str(a)
    #                 if (strExp) in listFns.keys() and "list_empty" in (strExp):
    #                     retStr += "(" + listFns[strExp] + ")" + " "
    #                 elif (strExp) in listFns.keys():
    #                     retStr += listFns[strExp]
    #                 else:
    #                     retStr += strExp + " "
    #         retStr += ")"
    #         return retStr

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

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        raise NotImplementedError()

    @staticmethod
    def toRosetteSimple(e: "Expr", value: str) -> str:
        retStr = "(" + value + " "
        for a in e.args:
            if isinstance(a, ValueRef) and a.name != "":
                retStr += "%s" % (a.name) + " "
            else:
                strExp = a.toRosette() if isinstance(a, Expr) else str(a)
                if (strExp) in Expr.listFns.keys() and "list_empty" in (strExp):
                    retStr += "(" + Expr.listFns[strExp] + ")" + " "
                elif (strExp) in Expr.listFns.keys():
                    retStr += Expr.listFns[strExp]
                else:
                    retStr += strExp + " "
        retStr += ")"
        return retStr

    def simplify(self) -> "Expr":
        self = self.mapArgs(lambda a: a.simplify() if isinstance(a, Expr) else a)
        if isinstance(self, And):
            filtered_args: typing.List[Expr] = []
            for arg in self.args:
                if isinstance(arg, Expr) and isinstance(arg, Lit):
                    if arg.args[0] == False:
                        return BoolLit(False)
                else:
                    filtered_args.append(arg)

            if len(filtered_args) == 0:
                return BoolLit(True)
            elif len(filtered_args) == 1:
                return filtered_args[0]
            else:
                return And(*filtered_args)
        else:
            return self

    def countVariableUses(self, into: Dict[str, int]) -> None:
        if isinstance(self, Var):
            if not (self.args[0] in into):
                into[self.args[0]] = 0
            into[self.args[0]] += 1
        else:
            for a in self.args:
                if isinstance(a, Expr):
                    a.countVariableUses(into)

    def collectKnowledge(
        self,
        constrained_elsewhere: typing.Set[str],
        into: Dict[str, "Expr"],
        conflicts: Dict[str, bool],
    ) -> None:
        if isinstance(self, Eq):
            if isinstance(self.args[0], Var) and (
                not self.args[0].args[0] in constrained_elsewhere
            ):
                if self.args[0].args[0] in into or self.args[0].args[0] in conflicts:
                    conflicts[self.args[0].args[0]] = True
                    del into[self.args[0].args[0]]
                else:
                    into[self.args[0].args[0]] = self.args[1]
            elif isinstance(self.args[1], Var) and (
                not self.args[1].args[0] in constrained_elsewhere
            ):
                if self.args[1].args[0] in into or self.args[1].args[0] in conflicts:
                    conflicts[self.args[1].args[0]] = True
                    del into[self.args[1].args[0]]
                else:
                    into[self.args[1].args[0]] = self.args[0]
        elif isinstance(self, And):
            for a in self.args:
                if isinstance(a, Expr):
                    a.collectKnowledge(constrained_elsewhere, into, conflicts)
        else:
            return

    def rewrite(self, mappings: Dict[str, "Expr"]) -> "Expr":
        if isinstance(self, Var):
            if self.args[0] in mappings:
                return mappings[self.args[0]]
            else:
                return self
        else:
            return self.mapArgs(
                lambda a: a.rewrite(mappings) if isinstance(a, Expr) else a
            )

    def optimizeUselessEquality(
        self, counts: Dict[str, int], new_vars: typing.Set["Expr"]
    ) -> "Expr":
        if isinstance(self, Eq):
            replacement_var = Var("useless_equality_%d" % len(new_vars), Bool())
            if isinstance(self.args[0], Var) and counts[self.args[0].args[0]] == 1:
                new_vars.add(replacement_var)
                return replacement_var
            elif isinstance(self.args[1], Var) and counts[self.args[1].args[0]] == 1:
                new_vars.add(replacement_var)
                return replacement_var
            elif isinstance(self.args[0], Var) and isinstance(self.args[1], Var):
                if self.args[0].args[0] == self.args[1].args[0]:
                    return BoolLit(True)
        elif isinstance(self, Implies):
            local_counts: Dict[str, int] = {}
            self.countVariableUses(local_counts)

            constrained_elsewhere = set(counts.keys())
            for key in local_counts.keys():
                if local_counts[key] == counts[key]:
                    constrained_elsewhere.remove(key)
            rewrites: Dict[str, "Expr"] = {}
            self.args[0].collectKnowledge(constrained_elsewhere, rewrites, {})

            counts_rhs: Dict[str, int] = {}
            self.args[1].countVariableUses(counts_rhs)

            for rewrite_var in list(rewrites.keys()):
                if not (isinstance(rewrites[rewrite_var], Var)):
                    if rewrite_var in counts_rhs and counts_rhs[rewrite_var] > 1:
                        del rewrites[rewrite_var]

            self = self.rewrite(rewrites)

        return self
        # XXX
        # return self.mapArgs(
        #     lambda a: a.optimizeUselessEquality(counts, new_vars)
        #     if isinstance(a, Expr)
        #     else a
        # ).simplify()


class Var(Expr):
    def __init__(self, name: str, ty: Type) -> None:
        Expr.__init__(self, ty, [name])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def __repr__(self) -> str:
        return self.args[0]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return str(self.args[0])

    def toSMT(self) -> str:
        return str(self.args[0])


# def Var(name: str, ty: Type) -> Expr:
#     return Expr(Expr.Kind.Var, ty, [name])


class Lit(Expr):
    def __init__(self, val: Union[bool, int, str], ty: Type) -> None:
        Expr.__init__(self, ty, [val])

    def val(self) -> Union[bool, int, str]:
        return self.args[0]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        if self.type == Bool():
            return "true" if self.args[0] else "false"
        else:
            return str(self.args[0])

    def toSMT(self) -> str:
        if self.type == Bool():
            return "true" if self.args[0] else "false"
        else:
            return str(self.args[0])


# def Lit(val: Union[bool, int, str], ty: Type) -> Expr:
#     return Expr(Expr.Kind.Lit, ty, [val])

# akc: not sure if this is needed
# def Object(ty: Type) -> Expr:
#     return Expr(Expr.Kind.Object, ty, {})


def IntLit(val: int) -> Expr:
    return Lit(val, Int())


def BoolIntLit(val: int) -> Expr:
    return Lit(val, BoolInt())


def BoolLit(val: bool) -> Expr:
    return Lit(val, Bool())


class Add(Expr):
    RosetteName = SMTName = "+"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        for arg in args:
            if parseTypeRef(arg.type) != parseTypeRef(args[0].type):
                raise Exception(
                    f"Args types not equal: {parseTypeRef(arg.type).erase()} and {parseTypeRef(args[0].type).erase()}"
                )
        Expr.__init__(self, Int(), args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Add(*args: Expr) -> Expr:
#     return Expr(Expr.Kind.Add, Int(), args)


class Sub(Expr):
    RosetteName = SMTName = "-"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        for arg in args:
            if parseTypeRef(arg.type) != parseTypeRef(args[0].type):
                raise Exception(
                    f"Args types not equal: {parseTypeRef(arg.type).erase()} and {parseTypeRef(args[0].type).erase()}"
                )
        Expr.__init__(self, Int(), args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Sub(*args: Expr) -> Expr:
#     return Expr(Expr.Kind.Sub, Int(), args)


class Mul(Expr):
    RosetteName = SMTName = "*"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        for arg in args:
            if parseTypeRef(arg.type) != parseTypeRef(args[0].type):
                raise Exception(
                    f"Args types not equal: {parseTypeRef(arg.type).erase()} and {parseTypeRef(args[0].type).erase()}"
                )
        Expr.__init__(self, Int(), args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Mul(*args: Expr) -> Expr:
#     return Expr(Expr.Kind.Mul, Int(), args)


class Eq(Expr):
    RosetteName = "equal?"
    SMTName = "="

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (parseTypeRef(e1.type).erase() == parseTypeRef(e2.type).erase()):
            raise Exception(
                f"Cannot compare values of different types: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
            )
        Expr.__init__(self, Bool(), [e1, e2])

    def e1(self) -> Expr:
        return self.args[0]  # type: ignore

    def e2(self) -> Expr:
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        name = "set-eq" if self.args[0].type.name == "Set" else self.RosetteName
        return Expr.toRosetteSimple(self, name)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Eq(e1: Expr, e2: Expr) -> Expr:
#     if not (parseTypeRef(e1.type).erase() == parseTypeRef(e2.type).erase()):
#         raise Exception(
#             f"Cannot compare values of different types: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
#         )
#     return Expr(Expr.Kind.Eq, Bool(), [e1, e2])


class Lt(Expr):
    RosetteName = SMTName = "<"

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (parseTypeRef(e1.type).erase() == parseTypeRef(e2.type).erase()):
            raise Exception(
                f"Cannot compare values of different types: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
            )
        Expr.__init__(self, Bool(), [e1, e2])

    def e1(self) -> Expr:
        return self.args[0]  # type: ignore

    def e2(self) -> Expr:
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Lt(e1: Expr, e2: Expr) -> Expr:
#     return Expr(Expr.Kind.Lt, Bool(), [e1, e2])


class Le(Expr):
    RosetteName = SMTName = "<="

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (parseTypeRef(e1.type).erase() == parseTypeRef(e2.type).erase()):
            raise Exception(
                f"Cannot compare values of different types: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
            )
        Expr.__init__(self, Bool(), [e1, e2])

    def e1(self) -> Expr:
        return self.args[0]  # type: ignore

    def e2(self) -> Expr:
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Le(e1: Expr, e2: Expr) -> Expr:
#     return Expr(Expr.Kind.Le, Bool(), [e1, e2])


class Gt(Expr):
    RosetteName = SMTName = ">"

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (parseTypeRef(e1.type).erase() == parseTypeRef(e2.type).erase()):
            raise Exception(
                f"Cannot compare values of different types: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
            )
        Expr.__init__(self, Bool(), [e1, e2])

    def e1(self) -> Expr:
        return self.args[0]  # type: ignore

    def e2(self) -> Expr:
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Gt(e1: Expr, e2: Expr) -> Expr:
#     return Expr(Expr.Kind.Gt, Bool(), [e1, e2])


class Ge(Expr):
    RosetteName = SMTName = ">="

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (parseTypeRef(e1.type).erase() == parseTypeRef(e2.type).erase()):
            raise Exception(
                f"Cannot compare values of different types: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
            )
        Expr.__init__(self, Bool(), [e1, e2])

    def e1(self) -> Expr:
        return self.args[0]  # type: ignore

    def e2(self) -> Expr:
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Ge(e1: Expr, e2: Expr) -> Expr:
#     return Expr(Expr.Kind.Ge, Bool(), [e1, e2])


class And(Expr):
    RosetteName = "&&"  # racket "and" short circuits!
    SMTName = "and"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        if not all(map(lambda e: e.type == Bool(), args)):
            raise Exception(f"Cannot apply AND to values of type {args}")
        Expr.__init__(self, Bool(), args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def And(*args: Expr) -> Expr:
#     return Expr(Expr.Kind.And, Bool(), args)


class Or(Expr):
    # XXX we should use || for rosette to avoid short circuiting
    RosetteName = SMTName = "or"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        if not all(map(lambda e: e.type == Bool(), args)):
            raise Exception(
                f"Cannot apply OR to values of type {map(lambda e: e.type, args)}"
            )
        Expr.__init__(self, Bool(), args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Or(*args: Expr) -> Expr:
#     if parseTypeRef(args[0].type) != Bool() or parseTypeRef(args[1].type) != Bool():
#         raise Exception(
#             f"Cannot apply OR to values of type {parseTypeRef(args[0].type).erase()}, {parseTypeRef(args[1].type).erase()}"
#         )
#     return Expr(Expr.Kind.Or, Bool(), args)


class Not(Expr):
    RosetteName = "!"
    SMTName = "not"

    def __init__(self, e: Expr) -> None:
        if e.type != Bool():
            raise Exception(f"Cannot apply NOT to value of type {e.type}")
        Expr.__init__(self, Bool(), [e])

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Not(e: Expr) -> Expr:
#     return Expr(Expr.Kind.Not, Bool(), [e])


class Implies(Expr):
    RosetteName = SMTName = "=>"

    def __init__(self, e1: Union[Expr, "MLInst"], e2: Union[Expr, "MLInst"]) -> None:
        if e1.type != Bool():  # type: ignore
            raise Exception(f"Cannot apply IMPLIES to value of type {e1.type}")  # type: ignore
        if e2.type != Bool():  # type: ignore
            raise Exception(f"Cannot apply IMPLIES to value of type {e2.type}")  # type: ignore
        Expr.__init__(self, Bool(), [e1, e2])

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Implies(e1: Union[Expr, "MLInst"], e2: Union[Expr, "MLInst"]) -> Expr:
#     return Expr(Expr.Kind.Implies, Bool(), [e1, e2])


class Ite(Expr):
    RosetteName = "if"
    SMTName = "ite"

    def __init__(self, c: Expr, e1: Expr, e2: Expr) -> None:
        if c.type != Bool():
            raise Exception(
                f"ITE condition must be Boolean and not value of type {c.type}"
            )
        if e1.type != e2.type:
            raise Exception(
                f"TE branches in ITE must have the same type: {e1.type}, {e2.type}"
            )
        Expr.__init__(self, e1.type, [c, e1, e2])

    def c(self) -> Expr:
        return self.args[0]  # type: ignore

    def e1(self) -> Expr:
        return self.args[1]  # type: ignore

    def e2(self) -> Expr:
        return self.args[2]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Ite(c: Expr, e1: Expr, e2: Expr) -> Expr:
#     if parseTypeRef(e1.type).erase() != parseTypeRef(e2.type).erase():
#         raise Exception(
#             f"Cannot return different types from ite: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
#         )
#     return Expr(Expr.Kind.Ite, e1.type, [c, e1, e2])


class Let(Expr):
    def __init__(self, v: Expr, e: Expr, e2: Expr) -> None:
        Expr.__init__(self, e2.type, [v, e, e2])

    def v(self) -> Expr:
        return self.args[0]  # type: ignore

    def e(self) -> Expr:
        return self.args[1]  # type: ignore

    def e2(self) -> Expr:
        return self.args[2]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return f"(let ([{self.args[0].toRosette()} {self.args[1].toRosette() if isinstance(self.args[1], Expr) else str(self.args[1])}]) {self.args[2].toRosette()})"

    def toSMT(self) -> str:
        return "(let ((%s %s)) %s)" % (
            self.args[0].toSMT(),
            self.args[1].toSMT(),
            self.args[2].toSMT(),
        )


# def Let(v: Expr, e: Expr, e2: Expr) -> Expr:
#     return Expr(Expr.Kind.Let, e2.type, [v, e, e2])


class Call(Expr):
    def __init__(self, name: str, returnT: Type, *arguments: Expr) -> None:
        Expr.__init__(self, returnT, [name, *arguments])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[1:]  # type: ignore

    def __repr__(self) -> str:
        return f"({self.args[0]}:{self.type} {' '.join(str(a) for a in self.args[1:])})"

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        if isinstance(self.args[0], str) or isinstance(self, CallValue):
            if isinstance(self.args[0], str) and (
                self.args[0].startswith("inv") or self.args[0].startswith("ps")
            ):
                callStr = "( " + "%s " % (str(self.args[0]))
                for a in self.args[1:]:
                    callStr += a.toRosette() + " "
                callStr += ")"
                return callStr
            elif isinstance(self.args[0], str) and self.args[0].startswith("list"):
                callStr = (
                    "("
                    + "%s"
                    % (
                        Expr.listFns[self.args[0]]
                        if self.args[0] in Expr.listFns.keys()
                        else self.args[0]
                    )
                    + " "
                )
                for a in self.args[1:]:
                    if isinstance(a, ValueRef) and a.name != "":
                        callStr += "%s " % (a.name)
                    else:
                        callStr += a.toRosette() + " "
                callStr += ")"
                return callStr
            else:
                return (
                    "("
                    + " ".join(
                        [
                            a.name
                            if isinstance(a, ValueRef) and a.name != ""
                            else a
                            if isinstance(a, str)
                            else a.toRosette()
                            for a in self.args
                        ]
                    )
                    + ")"
                )
        else:
            return " ".join(
                [
                    a.name
                    if isinstance(a, ValueRef) and a.name != ""
                    else str(a)
                    if isinstance(a, str)
                    else a.toRosette()
                    for a in self.args
                ]
            )

    def toSMT(self) -> str:
        noParens = isinstance(self, Call) and len(self.args) == 1
        retVal = []

        if self.args[0] == "set-create":
            return f"(as set.empty {self.type.toSMT()})"

        if self.args[0] == "tupleGet":
            argvals = self.args[:-1]
        else:
            argvals = self.args

        for idx, a in enumerate(argvals):
            if isinstance(a, ValueRef) and a.name != "":
                retVal.append(a.name)
            elif (str(a)) == "make-tuple":
                retVal.append("tuple%d" % (len(self.args[idx + 1 :])))
            elif (str(a)) == "tupleGet":
                if self.args[idx + 1].args[0] == "make-tuple":
                    retVal.append(
                        "tuple%d_get%d"
                        % (
                            len(self.args[idx + 1].args) - 1,
                            self.args[idx + 2].args[0],
                        )
                    )
                else:
                    # HACK: if function argument is a tuple, count I's in the mangled names of args to get number of elements in tuple
                    freq: typing.Counter[str] = Counter(
                        self.args[idx + 1].args[0].split("_")[1]
                    )
                    retVal.append(
                        "tuple%d_get%d" % (freq["i"], self.args[idx + 2].args[0])
                    )
            elif (str(a)).startswith("set-"):
                retVal.append("set.%s" % (str(a)[4:]))
            elif (str(a)).startswith("map-"):
                retVal.append("map_%s" % (str(a)[4:]))
            elif isinstance(a, str):
                retVal.append(str(a))
            else:
                retVal.append(a.toSMT())

        retT = ("" if noParens else "(") + " ".join(retVal) + ("" if noParens else ")")

        return retT


# def Call(name: str, returnT: Type, *args: Expr) -> Expr:
#     return Expr(Expr.Kind.Call, returnT, [name, *args])


class CallValue(Expr):
    def __init__(self, value: Expr, *arguments: Expr) -> None:
        Expr.__init__(self, value.type.args[0], [value, *arguments])

    def value(self) -> Expr:
        return self.args[0]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        if isinstance(self.args[0], str) or isinstance(self, CallValue):
            if isinstance(self.args[0], str) and (
                self.args[0].startswith("inv") or self.args[0].startswith("ps")
            ):
                callStr = "( " + "%s " % (str(self.args[0]))
                for a in self.args[1:]:
                    callStr += a.toRosette() + " "
                callStr += ")"
                return callStr
            elif isinstance(self.args[0], str) and self.args[0].startswith("list"):
                callStr = (
                    "("
                    + "%s"
                    % (
                        Expr.listFns[self.args[0]]
                        if self.args[0] in Expr.listFns.keys()
                        else self.args[0]
                    )
                    + " "
                )
                for a in self.args[1:]:
                    if isinstance(a, ValueRef) and a.name != "":
                        callStr += "%s " % (a.name)
                    else:
                        callStr += a.toRosette() + " "
                callStr += ")"
                return callStr
            else:
                return (
                    "("
                    + " ".join(
                        [
                            a.name
                            if isinstance(a, ValueRef) and a.name != ""
                            else a
                            if isinstance(a, str)
                            else a.toRosette()
                            for a in self.args
                        ]
                    )
                    + ")"
                )
        else:
            return " ".join(
                [
                    a.name
                    if isinstance(a, ValueRef) and a.name != ""
                    else str(a)
                    if isinstance(a, str)
                    else a.toRosette()
                    for a in self.args
                ]
            )

    def toSMT(self) -> str:
        noParens = isinstance(self, Call) and len(self.args) == 1
        retVal = []

        if self.args[0] == "set-create":
            return f"(as set.empty {self.type.toSMT()})"

        if self.args[0] == "tupleGet":
            argvals = self.args[:-1]
        else:
            argvals = self.args

        for idx, a in enumerate(argvals):
            if isinstance(a, ValueRef) and a.name != "":
                retVal.append(a.name)
            elif (str(a)) == "make-tuple":
                retVal.append("tuple%d" % (len(self.args[idx + 1 :])))
            elif (str(a)) == "tupleGet":
                if self.args[idx + 1].args[0] == "make-tuple":
                    retVal.append(
                        "tuple%d_get%d"
                        % (
                            len(self.args[idx + 1].args) - 1,
                            self.args[idx + 2].args[0],
                        )
                    )
                else:
                    # HACK: if function argument is a tuple, count I's in the mangled names of args to get number of elements in tuple
                    freq: typing.Counter[str] = Counter(
                        self.args[idx + 1].args[0].split("_")[1]
                    )
                    retVal.append(
                        "tuple%d_get%d" % (freq["i"], self.args[idx + 2].args[0])
                    )
            elif (str(a)).startswith("set-"):
                retVal.append("set.%s" % (str(a)[4:]))
            elif (str(a)).startswith("map-"):
                retVal.append("map_%s" % (str(a)[4:]))
            elif isinstance(a, str):
                retVal.append(str(a))
            else:
                retVal.append(a.toSMT())

        retT = ("" if noParens else "(") + " ".join(retVal) + ("" if noParens else ")")

        return retT


# def CallValue(value: Expr, *args: Expr) -> Expr:
#     return Expr(Expr.Kind.CallValue, value.type.args[0], [value, *args])


class Assert(Expr):
    RosetteName = SMTName = "assert"

    def __init__(self, e: Expr) -> None:
        Expr.__init__(self, Bool(), [e])

    def e(self) -> Expr:
        return self.args[0]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)


# def Assert(e: Expr) -> Expr:
#     return Expr(Expr.Kind.Assert, Bool(), [e])


class Constraint(Expr):
    def __init__(self, e: Expr) -> None:
        Expr.__init__(self, Bool(), [e])

    def e(self) -> Expr:
        return self.args[0]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        raise Exception("NYI")
        # return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        raise Exception("NYI")
        # return Expr.toSMTSimple(self, self.SMTName)


# def Constraint(e: Expr) -> Expr:
#     return Expr(Expr.Kind.Constraint, Bool(), [e])

## tuple functions
class Tuple(Expr):
    def __init__(self, *args: Expr) -> None:
        Expr.__init__(self, TupleT(*[a.type for a in args]), args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        # original code was "(make-tuple %s) % " ".join(["%s" % str(arg) for arg in self.args])
        # but arg can be a ValueRef and calling str on it will return both type and name e.g., i32 %arg
        return Call("make-tuple", self.type, *self.args).toRosette()

    def toSMT(self) -> str:
        args = " ".join(
            [
                arg.name if isinstance(arg, ValueRef) else arg.toSMT()
                for arg in self.args
            ]
        )
        return "(tuple%d %s)" % (len(self.args), args)


# def Tuple(*args: Expr) -> Expr:
#     return Expr(Expr.Kind.Tuple, TupleT(*[a.type for a in args]), args)


class TupleGet(Expr):
    def __init__(self, t: Expr, i: Expr) -> None:
        Expr.__init__(self, t.type.args[i.args[0]], [t, i])

    def t(self) -> Expr:
        return self.args[0]  # type: ignore

    def i(self) -> Expr:
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return "(tupleGet %s)" % " ".join(["%s" % arg.toRosette() for arg in self.args])

    def toSMT(self) -> str:
        # example: generate (tuple2_get0 t)
        return "(tuple%d_get%d %s)" % (
            len(self.args[0].type.args),
            self.args[1].args[0],
            self.args[0].toSMT(),
        )  # args[1] must be an int literal


# def TupleGet(t: Expr, i: Expr) -> Expr:
#     return Expr(Expr.Kind.TupleGet, t.type.args[i.args[0]], [t, i])


class Axiom(Expr):
    def __init__(self, e: Expr, *vars: Expr) -> None:
        Expr.__init__(self, Bool(), [e, *vars])

    def e(self) -> Expr:
        return self.args[0]  # type: ignore

    def vars(self) -> typing.List[Expr]:
        return self.args[1:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return ""  # axioms are only for verification

    def toSMT(self) -> str:
        vs = ["(%s %s)" % (a.args[0], a.type) for a in self.args[1:]]
        return "(assert (forall ( %s ) %s ))" % (" ".join(vs), self.args[0].toSMT())


# def Axiom(e: Expr, *vars: Expr) -> Expr:
#     return Expr(Expr.Kind.Axiom, Bool(), [e, *vars])

# the body of a synth-fun
class Synth(Expr):
    def __init__(self, name: str, body: Expr, *args: Expr) -> None:
        Expr.__init__(self, body.type, [name, body, *args])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def body(self) -> Expr:
        return self.args[1]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[2:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        cnts = Expr.findCommonExprs(self.args[1], {})
        commonExprs = list(
            filter(
                lambda k: isinstance(k, Choose),
                cnts.keys(),
            )
        )
        rewritten = Expr.replaceExprs(self.args[1], commonExprs, PrintMode.Rosette)

        # rewrite common exprs to use each other
        commonExprs = [
            Expr.replaceExprs(e, commonExprs, PrintMode.Rosette, skipTop=True)
            for e in commonExprs
        ]

        args = " ".join(
            "%s" % a.name
            if isinstance(a, ValueRef)
            else str(a)
            if isinstance(a, str)
            else a.toRosette()
            for a in self.args[2:]
        )

        defs = "[rv (choose %s)]\n" % rewritten.toRosette()

        if writeChoicesTo != None:
            for i, e in enumerate(commonExprs):
                writeChoicesTo[f"v{i}"] = e  # type: ignore

        defs = defs + "\n".join(
            "%s %s)]" % ("[v%d (choose" % i, e.toRosette())
            for i, e in enumerate(commonExprs)
        )

        return "(define-grammar (%s_gram %s)\n %s\n)" % (self.args[0], args, defs)

    def toSMT(self) -> str:
        cnts = Expr.findCommonExprs(self.args[1], {})
        commonExprs = list(
            filter(
                lambda k: isinstance(k, Choose),
                cnts.keys(),
            )
        )
        rewritten = Expr.replaceExprs(self.args[1], commonExprs, PrintMode.SMT)

        # rewrite common exprs to use each other
        commonExprs = [
            Expr.replaceExprs(e, commonExprs, PrintMode.SMT, skipTop=True)
            for e in commonExprs
        ]

        decls = "((rv %s) %s)" % (
            self.type.toSMT(),
            " ".join(
                "(%s %s)" % ("v%d" % i, parseTypeRef(e.type).toSMT())
                for i, e in enumerate(commonExprs)
            ),
        )
        defs = "(rv %s %s)\n" % (
            self.type.toSMT(),
            rewritten.toSMT()
            if isinstance(rewritten, Choose)
            else "(%s)" % rewritten.toSMT(),
        )
        defs = defs + "\n".join(
            "(%s %s %s)"
            % (
                "v%d" % i,
                parseTypeRef(e.type).toSMT(),
                e.toSMT() if isinstance(self, Choose) else f"({e.toSMT()})",
            )
            for i, e in enumerate(commonExprs)
        )

        body = decls + "\n" + "(" + defs + ")"

        declarations = []
        for a in self.args[2:]:
            if isinstance(a, ValueRef):
                declarations.append((a.name, parseTypeRef(a.type)))
            else:
                declarations.append((a.args[0], a.type))

        args = " ".join("(%s %s)" % (d[0], d[1].toSMT()) for d in declarations)
        return "(synth-fun %s (%s) %s\n%s)" % (
            self.args[0],
            args,
            self.type.toSMT(),
            body,
        )


# def Synth(name: str, body: Expr, *args: Expr) -> Expr:
#     return Expr(Expr.Kind.Synth, body.type, [name, body, *args])


class Choose(Expr):
    def __init__(self, *args: Expr) -> None:
        if not all(parseTypeRef(a.type) == parseTypeRef(args[0].type) for a in args):
            raise Exception(
                "Choose args are of different types: %s"
                % " ".join(str(a) for a in args)
            )
        Expr.__init__(self, args[0].type, args)

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[1:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return " ".join(
            [
                a.name
                if isinstance(a, ValueRef) and a.name != ""
                else str(a)
                if isinstance(a, str)
                else a.toRosette()
                for a in self.args
            ]
        )

    def toSMT(self) -> str:
        noParens = isinstance(self, Call) and len(self.args) == 1
        retVal = []

        if self.args[0] == "set-create":
            return f"(as set.empty {self.type.toSMT()})"

        if self.args[0] == "tupleGet":
            argvals = self.args[:-1]
        else:
            argvals = self.args

        for idx, a in enumerate(argvals):
            if isinstance(a, ValueRef) and a.name != "":
                retVal.append(a.name)
            elif (str(a)) == "make-tuple":
                retVal.append("tuple%d" % (len(self.args[idx + 1 :])))
            elif (str(a)) == "tupleGet":
                if self.args[idx + 1].args[0] == "make-tuple":
                    retVal.append(
                        "tuple%d_get%d"
                        % (
                            len(self.args[idx + 1].args) - 1,
                            self.args[idx + 2].args[0],
                        )
                    )
                else:
                    # HACK: if function argument is a tuple, count I's in the mangled names of args to get number of elements in tuple
                    freq: typing.Counter[str] = Counter(
                        self.args[idx + 1].args[0].split("_")[1]
                    )
                    retVal.append(
                        "tuple%d_get%d" % (freq["i"], self.args[idx + 2].args[0])
                    )
            elif (str(a)).startswith("set-"):
                retVal.append("set.%s" % (str(a)[4:]))
            elif (str(a)).startswith("map-"):
                retVal.append("map_%s" % (str(a)[4:]))
            elif isinstance(a, str):
                retVal.append(str(a))
            else:
                retVal.append(a.toSMT())

        retT = ("" if noParens else "(") + " ".join(retVal) + ("" if noParens else ")")

        return retT


# def Choose(*args: Expr) -> Expr:
#     if len(args) == 1:
#         return args[0]
#     else:
#         if not all(parseTypeRef(a.type) == parseTypeRef(args[0].type) for a in args):
#             raise Exception(
#                 "Choose args are of different types: %s"
#                 % " ".join(str(a) for a in args)
#             )
#         return Expr(Expr.Kind.Choose, args[0].type, args)


class FnDecl(Expr):
    def __init__(
        self, name: str, returnT: Type, body: Union[Expr, str], *args: Expr
    ) -> None:
        Expr.__init__(self, Fn(returnT, *[a.type for a in args]), [name, body, *args])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def returnT(self) -> Type:
        return self.type.args[0]

    def body(self) -> Union[Expr, str]:
        return self.args[1]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[2:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        if self.args[1] is None:  # uninterpreted function
            args_type = " ".join(["%s" % toRosetteType(a.type) for a in self.args[2:]])
            return "(define-symbolic %s (~> %s %s))" % (
                self.args[0],
                args_type,
                toRosetteType(self.type),
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
                "define" if isinstance(self, FnDeclNonRecursive) else "define-bounded"
            )

            return "(%s (%s %s) \n%s)" % (
                def_str,
                self.args[0],
                args,
                self.args[1].toRosette(),
            )

    def toSMT(self) -> str:
        if isinstance(self, FnDefine) or self.args[1] is None:  # uninterpreted function
            args_type = " ".join(parseTypeRef(a.type).toSMT() for a in self.args[2:])
            return "(declare-fun %s (%s) %s)" % (
                self.args[0],
                args_type,
                parseTypeRef(self.type),
            )

        else:
            declarations = []
            for a in self.args[2:]:
                if isinstance(a, ValueRef):
                    declarations.append((a.name, parseTypeRef(a.type)))
                else:
                    declarations.append((a.args[0], a.type))

            args = " ".join("(%s %s)" % (d[0], d[1].toSMT()) for d in declarations)

            def_str = "define-fun-rec" if isinstance(self, FnDecl) else "define-fun"

            return "(%s %s (%s) %s\n%s)" % (
                def_str,
                self.args[0],
                args,
                (
                    self.type if self.type.name != "Function" else self.type.args[0]
                ).toSMT(),
                self.args[1] if isinstance(self.args[1], str) else self.args[1].toSMT(),
            )


# def FnDecl(name: str, returnT: Type, body: Union[Expr, str], *args: Expr) -> Expr:
#     return Expr(
#         Expr.Kind.FnDecl, Fn(returnT, *[a.type for a in args]), [name, body, *args]
#     )


class FnDefine(Expr):
    def __init__(self, name: str, returnT: Type, *args: Expr) -> None:
        Expr.__init__(self, Fn(returnT, *[a.type for a in args]), [name, *args])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def returnT(self) -> Type:
        return self.type.args[0]

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[1:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return ""  # only for verification

    def toSMT(self) -> str:
        if isinstance(self, FnDefine) or self.args[1] is None:  # uninterpreted function
            args_type = " ".join(parseTypeRef(a.type).toSMT() for a in self.args[2:])
            return "(declare-fun %s (%s) %s)" % (
                self.args[0],
                args_type,
                parseTypeRef(self.type),
            )

        else:
            declarations = []
            for a in self.args[2:]:
                if isinstance(a, ValueRef):
                    declarations.append((a.name, parseTypeRef(a.type)))
                else:
                    declarations.append((a.args[0], a.type))

            args = " ".join("(%s %s)" % (d[0], d[1].toSMT()) for d in declarations)

            def_str = "define-fun-rec" if isinstance(self, FnDecl) else "define-fun"

            return "(%s %s (%s) %s\n%s)" % (
                def_str,
                self.args[0],
                args,
                (
                    self.type if self.type.name != "Function" else self.type.args[0]
                ).toSMT(),
                self.args[1] if isinstance(self.args[1], str) else self.args[1].toSMT(),
            )


# def FnDefine(name: str, returnT: Type, *args: Expr) -> Expr:
#     return Expr(Expr.Kind.FnDefine, Fn(returnT, *[a.type for a in args]), [name, *args])


class Lambda(Expr):
    def __init__(self, returnT: Type, body: Expr, *args: Expr) -> None:
        Expr.__init__(self, Fn(returnT, *[a.type for a in args]), [body, *args])

    def body(self) -> Expr:
        return self.args[0]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[1:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        args = " ".join(
            [
                "%s" % (a.name)
                if isinstance(a, ValueRef) and a.name != ""
                else "%s" % (a.args[0])
                for a in self.args[1:]
            ]
        )

        return "(lambda (%s) %s)" % (
            args,
            self.args[0].toRosette(),
        )

    def toSMT(self) -> str:
        # TODO(shadaj): extract during filtering assuming no captures
        raise Exception("Lambda not supported")


# def Lambda(returnT: Type, body: Expr, *args: Expr) -> Expr:
#     return Expr(Expr.Kind.Lambda, Fn(returnT, *[a.type for a in args]), [body, *args])


class FnDeclNonRecursive(Expr):
    def __init__(
        self, name: str, returnT: Type, body: Union[Expr, str], *args: Expr
    ) -> None:
        Expr.__init__(self, Fn(returnT, *[a.type for a in args]), [name, body, *args])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def returnT(self) -> Type:
        return self.type.args[0]

    def body(self) -> Union[Expr, str]:
        return self.args[1]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[2:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        if self.args[1] is None:  # uninterpreted function
            args_type = " ".join(["%s" % toRosetteType(a.type) for a in self.args[2:]])
            return "(define-symbolic %s (~> %s %s))" % (
                self.args[0],
                args_type,
                toRosetteType(self.type),
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
                "define" if isinstance(self, FnDeclNonRecursive) else "define-bounded"
            )

            return "(%s (%s %s) \n%s)" % (
                def_str,
                self.args[0],
                args,
                self.args[1].toRosette(),
            )

    def toSMT(self) -> str:
        if isinstance(self, FnDefine) or self.args[1] is None:  # uninterpreted function
            args_type = " ".join(parseTypeRef(a.type).toSMT() for a in self.args[2:])
            return "(declare-fun %s (%s) %s)" % (
                self.args[0],
                args_type,
                parseTypeRef(self.type),
            )

        else:
            declarations = []
            for a in self.args[2:]:
                if isinstance(a, ValueRef):
                    declarations.append((a.name, parseTypeRef(a.type)))
                else:
                    declarations.append((a.args[0], a.type))

            args = " ".join("(%s %s)" % (d[0], d[1].toSMT()) for d in declarations)

            def_str = "define-fun-rec" if isinstance(self, FnDecl) else "define-fun"

            return "(%s %s (%s) %s\n%s)" % (
                def_str,
                self.args[0],
                args,
                (
                    self.type if self.type.name != "Function" else self.type.args[0]
                ).toSMT(),
                self.args[1] if isinstance(self.args[1], str) else self.args[1].toSMT(),
            )


# def FnDeclNonRecursive(
#     name: str, returnT: Type, body: Union[Expr, str], *args: Expr
# ) -> Expr:
#     return Expr(
#         Expr.Kind.FnDeclNonRecursive,
#         Fn(returnT, *[a.type for a in args]),
#         [name, body, *args],
#     )


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

    def __init__(
        self, opcode: str, *operands: Union["MLInst", Expr, ValueRef], name: str = ""
    ) -> None:
        self.opcode = opcode
        self.operands = operands
        self.name = name

    def __str__(self) -> str:
        prefix = "%s = " % self.name if self.name else ""

        if self.opcode == MLInst.Kind.Call:
            return "%scall %s %s(%s)" % (
                prefix,
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
    elif tyStr.startswith("%struct.tup."):
        retType = [Int() for i in range(int(tyStr[-2]) + 1)]
        return TupleT(*retType)
    elif tyStr.startswith("%struct.tup"):
        # ToDo FIX return type for multiple values
        return TupleT(Int(), Int())
    else:
        raise Exception("NYI %s" % t)


def toRosetteType(t: Type) -> str:
    if t == Int():
        return "integer?"
    elif t == Bool():
        return "boolean?"
    else:
        raise Exception("NYI: %s" % t)

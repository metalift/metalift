from enum import Enum

from llvmlite.binding import ValueRef, TypeRef
from collections import Counter
import typing
from typing import Any, Callable, Dict, Union


class PrintMode(Enum):
    SMT = 0
    Rosette = 1


class Type:
    def __init__(self, name: str, *args: "Type") -> None:
        self.name = name
        self.args = args

    def toSMT(self) -> str:
        if (
            self.name == "Int"
            or self.name == "ClockInt"
            or self.name == "EnumInt"
            or self.name == "OpaqueInt"
        ):
            return "Int"
        elif self.name == "Bool":
            return "Bool"
        elif self.name == "String":
            return "String"
        elif self.name == "Tuple":
            args = " ".join(a.toSMT() for a in self.args)
            return "(Tuple%d %s)" % (len(self.args), args)
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
            or self.name == "EnumInt"
            or self.name == "OpaqueInt"
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


def EnumInt() -> Type:
    return Type("EnumInt")


def OpaqueInt() -> Type:
    return Type("OpaqueInt")


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


# first two types are not optional
def Tuple(e1T: Type, e2T: Type, *elemT: Type) -> Type:
    return Type("Tuple", e1T, e2T, *elemT)


class Expr:
    class Kind(Enum):
        Var = "var"
        Lit = "lit"
        Object = "obj"

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
        Let = "let"

        Call = "call"
        CallValue = "callvalue"

        Assert = "assert"
        Constraint = "constraint"
        Axiom = "axiom"
        Synth = "synth"
        Choose = "choose"
        FnDecl = "fndecl"
        FnDeclNonRecursive = "fndeclnonrecursive"
        Lambda = "lambda"

        Tuple = "tuple"
        TupleGet = "tupleGet"

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
        mode: PrintMode,
        skipTop: bool = False,
    ) -> Union["Expr", ValueRef]:
        # skipTop is used to ignore the top-level match when simplifying a common expr
        if e not in commonExprs or skipTop:
            if isinstance(e, Expr):
                newArgs = [Expr.replaceExprs(arg, commonExprs, mode) for arg in e.args]
                return Expr(e.kind, e.type, newArgs)
            else:
                return e  # ValueRef or TypeRef
        else:
            assert isinstance(e, Expr)
            if mode == PrintMode.Rosette:
                return Var("(v%d)" % commonExprs.index(e), e.type)
            else:
                return Var("v%d" % commonExprs.index(e), e.type)

    def __repr__(self) -> str:
        if self.kind == Expr.Kind.Var:
            return self.args[0]  # type: ignore
        elif self.kind == Expr.Kind.Call:
            return "(%s:%s %s)" % (
                self.args[0],
                self.type,
                " ".join(str(a) for a in self.args[1:]),
            )
        else:
            return "(%s:%s %s)" % (
                self.kind.name,
                self.type,
                " ".join(str(a) for a in self.args),
            )

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

    def toSMT(self) -> str:
        kind = self.kind
        if kind == Expr.Kind.Var or kind == Expr.Kind.Lit:
            if kind == Expr.Kind.Lit and self.type == Bool():
                if self.args[0] == True:
                    return "true"
                else:
                    return "false"
            else:
                return str(self.args[0])

        elif (
            kind == Expr.Kind.Call
            or kind == Expr.Kind.CallValue
            or kind == Expr.Kind.Choose
        ):
            noParens = kind == Expr.Kind.Call and len(self.args) == 1
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
                elif isinstance(a, str):
                    retVal.append(str(a))
                else:
                    retVal.append(a.toSMT())

            retT = (
                ("" if noParens else "(") + " ".join(retVal) + ("" if noParens else ")")
            )

            return retT

        elif kind == Expr.Kind.Synth:
            cnts = Expr.findCommonExprs(self.args[1], {})
            commonExprs = list(
                filter(
                    lambda k: k.kind == Expr.Kind.Choose,
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
                if rewritten.kind == Expr.Kind.Choose
                else "(%s)" % rewritten.toSMT(),
            )
            defs = defs + "\n".join(
                "(%s %s %s)"
                % (
                    "v%d" % i,
                    parseTypeRef(e.type).toSMT(),
                    e.toSMT() if e.kind == Expr.Kind.Choose else f"({e.toSMT()})",
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

        elif kind == Expr.Kind.Axiom:
            vs = ["(%s %s)" % (a.args[0], a.type) for a in self.args[1:]]
            return "(assert (forall ( %s ) %s ))" % (" ".join(vs), self.args[0].toSMT())
        elif kind == Expr.Kind.Lambda:
            # TODO(shadaj): extract during filtering assuming no captures
            raise Exception("Lambda not supported")
        elif kind == Expr.Kind.FnDecl or kind == Expr.Kind.FnDeclNonRecursive:
            if self.args[1] is None:  # uninterpreted function
                args_type = " ".join(
                    parseTypeRef(a.type).toSMT() for a in self.args[2:]
                )
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

                def_str = "define-fun-rec" if kind == Expr.Kind.FnDecl else "define-fun"

                return "(%s %s (%s) %s\n%s)" % (
                    def_str,
                    self.args[0],
                    args,
                    (
                        self.type if self.type.name != "Function" else self.type.args[0]
                    ).toSMT(),
                    self.args[1]
                    if isinstance(self.args[1], str)
                    else self.args[1].toSMT(),
                )

        elif kind == Expr.Kind.Tuple:
            args = " ".join(
                [
                    arg.name if isinstance(arg, ValueRef) else arg.toSMT()
                    for arg in self.args
                ]
            )
            return "(tuple%d %s)" % (len(self.args), args)

        elif kind == Expr.Kind.TupleGet:
            # example: generate (tuple2_get0 t)
            return "(tuple%d_get%d %s)" % (
                len(self.args[0].type.args),
                self.args[1].args[0],
                self.args[0].toSMT(),
            )  # args[1] must be an int literal
        elif kind == Expr.Kind.Let:
            return "(let ((%s %s)) %s)" % (
                self.args[0].toSMT(),
                self.args[1].toSMT(),
                self.args[2].toSMT(),
            )
        else:
            value = self.kind.value
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
                        for a in self.args
                    ]
                )
                + ")"
            )

    def toRosette(self) -> str:
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

        elif (
            kind == Expr.Kind.Call
            or kind == Expr.Kind.CallValue
            or kind == Expr.Kind.Choose
        ):
            if isinstance(self.args[0], str) or kind == Expr.Kind.CallValue:
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

        elif kind == Expr.Kind.Synth:
            cnts = Expr.findCommonExprs(self.args[1], {})
            commonExprs = list(
                filter(
                    lambda k: k.kind == Expr.Kind.Choose,
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

            defs = defs + "\n".join(
                "%s %s)]" % ("[v%d (choose" % i, e.toRosette())
                for i, e in enumerate(commonExprs)
            )

            return "(define-grammar (%s_gram %s)\n %s\n)" % (self.args[0], args, defs)

        elif kind == Expr.Kind.Axiom:
            return ""  # axioms are only for verification
        elif kind == Expr.Kind.Lambda:
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
        elif kind == Expr.Kind.FnDecl or kind == Expr.Kind.FnDeclNonRecursive:
            if self.args[1] is None:  # uninterpreted function
                args_type = " ".join(
                    ["%s" % toRosetteType(a.type) for a in self.args[2:]]
                )
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
                    "define"
                    if kind == Expr.Kind.FnDeclNonRecursive
                    else "define-bounded"
                )

                return "(%s (%s %s) \n%s)" % (
                    def_str,
                    self.args[0],
                    args,
                    self.args[1].toRosette(),
                )

        elif kind == Expr.Kind.Tuple:
            # original code was "(make-tuple %s) % " ".join(["%s" % str(arg) for arg in self.args])
            # but arg can be a ValueRef and calling str on it will return both type and name e.g., i32 %arg
            return Call("make-tuple", self.type, *self.args).toRosette()

        elif kind == Expr.Kind.TupleGet:
            return "(tupleGet %s)" % " ".join(
                ["%s" % arg.toRosette() for arg in self.args]
            )
        elif kind == Expr.Kind.Let:
            return f"(let ([{self.args[0].toRosette()} {self.args[1].toRosette()}]) {self.args[2].toRosette()})"
        else:
            if kind == Expr.Kind.And:
                value = "&&"
            elif kind == Expr.Kind.Eq:
                if self.args[0].type.name == "Set":
                    value = "set-eq"
                else:
                    value = "equal?"
            elif kind == Expr.Kind.Ite:
                value = "if"
            else:
                value = self.kind.value

            retStr = "(" + value + " "
            for a in self.args:
                if isinstance(a, ValueRef) and a.name != "":
                    retStr += "%s" % (a.name) + " "
                else:
                    strExp = a.toRosette() if isinstance(a, Expr) else str(a)
                    if (strExp) in listFns.keys() and "list_empty" in (strExp):
                        retStr += "(" + listFns[strExp] + ")" + " "
                    elif (strExp) in listFns.keys():
                        retStr += listFns[strExp]
                    else:
                        retStr += strExp + " "
            retStr += ")"
            return retStr

    def simplify(self) -> "Expr":
        self = self.mapArgs(lambda a: a.simplify() if isinstance(a, Expr) else a)
        if self.kind == Expr.Kind.And:
            filtered_args: typing.List[Expr] = []
            for arg in self.args:
                if isinstance(arg, Expr) and arg.kind == Expr.Kind.Lit:
                    if arg.args[0] == False:
                        return BoolLit(False)
                else:
                    filtered_args.append(arg)

            if len(filtered_args) == 0:
                return BoolLit(True)
            elif len(filtered_args) == 1:
                return filtered_args[0]
            else:
                return Expr(Expr.Kind.And, Bool(), filtered_args)
        else:
            return self

    def countVariableUses(self, into: Dict[str, int]) -> None:
        if self.kind == Expr.Kind.Var:
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
        if self.kind == Expr.Kind.Eq:
            if self.args[0].kind == Expr.Kind.Var and (
                not self.args[0].args[0] in constrained_elsewhere
            ):
                if self.args[0].args[0] in into or self.args[0].args[0] in conflicts:
                    conflicts[self.args[0].args[0]] = True
                    del into[self.args[0].args[0]]
                else:
                    into[self.args[0].args[0]] = self.args[1]
            elif self.args[1].kind == Expr.Kind.Var and (
                not self.args[1].args[0] in constrained_elsewhere
            ):
                if self.args[1].args[0] in into or self.args[1].args[0] in conflicts:
                    conflicts[self.args[1].args[0]] = True
                    del into[self.args[1].args[0]]
                else:
                    into[self.args[1].args[0]] = self.args[0]
        elif self.kind == Expr.Kind.And:
            for a in self.args:
                if isinstance(a, Expr):
                    a.collectKnowledge(constrained_elsewhere, into, conflicts)
        else:
            return

    def rewrite(self, mappings: Dict[str, "Expr"]) -> "Expr":
        if self.kind == Expr.Kind.Var:
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
        if self.kind == Expr.Kind.Eq:
            replacement_var = Var("useless_equality_%d" % len(new_vars), Bool())
            if self.args[0].kind == Expr.Kind.Var and counts[self.args[0].args[0]] == 1:
                new_vars.add(replacement_var)
                return replacement_var
            elif (
                self.args[1].kind == Expr.Kind.Var and counts[self.args[1].args[0]] == 1
            ):
                new_vars.add(replacement_var)
                return replacement_var
            elif (
                self.args[0].kind == Expr.Kind.Var
                and self.args[1].kind == Expr.Kind.Var
            ):
                if self.args[0].args[0] == self.args[1].args[0]:
                    return BoolLit(True)
        elif self.kind == Expr.Kind.Implies:
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
                if not (rewrites[rewrite_var].kind == Expr.Kind.Var):
                    if rewrite_var in counts_rhs and counts_rhs[rewrite_var] > 1:
                        del rewrites[rewrite_var]

            self = self.rewrite(rewrites)

        return self.mapArgs(
            lambda a: a.optimizeUselessEquality(counts, new_vars)
            if isinstance(a, Expr)
            else a
        ).simplify()


def Var(name: str, ty: Type) -> Expr:
    return Expr(Expr.Kind.Var, ty, [name])


def Lit(val: Union[bool, int, str], ty: Type) -> Expr:
    return Expr(Expr.Kind.Lit, ty, [val])


def Object(ty: Type) -> Expr:
    return Expr(Expr.Kind.Object, ty, {})


def IntLit(val: int) -> Expr:
    return Lit(val, Int())


def EnumIntLit(val: int) -> Expr:
    return Lit(val, EnumInt())


def BoolLit(val: bool) -> Expr:
    return Lit(val, Bool())


def Add(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Add, Int(), args)


def Sub(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Sub, Int(), args)


def Mul(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Mul, Int(), args)


def Eq(e1: Expr, e2: Expr) -> Expr:
    if not (parseTypeRef(e1.type).erase() == parseTypeRef(e2.type).erase()):
        raise Exception(
            f"Cannot compare values of different types: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
        )
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
    if parseTypeRef(e1.type).erase() != parseTypeRef(e2.type).erase():
        raise Exception(
            f"Cannot return different types from ite: {parseTypeRef(e1.type).erase()} and {parseTypeRef(e2.type).erase()}"
        )
    return Expr(Expr.Kind.Ite, e1.type, [c, e1, e2])


def Let(v: Expr, e: Expr, e2: Expr) -> Expr:
    return Expr(Expr.Kind.Let, e2.type, [v, e, e2])


def Call(name: str, returnT: Type, *args: Expr) -> Expr:
    return Expr(Expr.Kind.Call, returnT, [name, *args])


def CallValue(value: Expr, *args: Expr) -> Expr:
    return Expr(Expr.Kind.CallValue, value.type.args[0], [value, *args])


def Assert(e: Expr) -> Expr:
    return Expr(Expr.Kind.Assert, Bool(), [e])


def Constraint(e: Expr) -> Expr:
    return Expr(Expr.Kind.Constraint, Bool(), [e])


## tuple functions
def MakeTuple(*args: Expr) -> Expr:
    return Expr(Expr.Kind.Tuple, Tuple(*[a.type for a in args]), args)


def TupleGet(t: Expr, i: Expr) -> Expr:
    return Expr(Expr.Kind.TupleGet, t.type.args[i.args[0]], [t, i])


def Axiom(e: Expr, *vars: Expr) -> Expr:
    return Expr(Expr.Kind.Axiom, Bool(), [e, *vars])


# the body of a synth-fun
def Synth(name: str, body: Expr, *args: Expr) -> Expr:
    return Expr(Expr.Kind.Synth, body.type, [name, body, *args])


def Choose(*args: Expr) -> Expr:
    if len(args) == 1:
        return args[0]
    else:
        if not all(parseTypeRef(a.type) == parseTypeRef(args[0].type) for a in args):
            raise Exception(
                "Choose args are of different types: %s"
                % " ".join(str(a) for a in args)
            )
        return Expr(Expr.Kind.Choose, args[0].type, args)


def FnDecl(name: str, returnT: Type, body: Union[Expr, str], *args: Expr) -> Expr:
    return Expr(
        Expr.Kind.FnDecl, Fn(returnT, *[a.type for a in args]), [name, body, *args]
    )


def Lambda(returnT: Type, body: Expr, *args: Expr) -> Expr:
    return Expr(Expr.Kind.Lambda, Fn(returnT, *[a.type for a in args]), [body, *args])


def FnDeclNonRecursive(
    name: str, returnT: Type, body: Union[Expr, str], *args: Expr
) -> Expr:
    return Expr(
        Expr.Kind.FnDeclNonRecursive,
        Fn(returnT, *[a.type for a in args]),
        [name, body, *args],
    )


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
        return Tuple(*retType)
    elif tyStr.startswith("%struct.tup"):
        # ToDo FIX return type for multiple values
        return Tuple(Int(), Int())
    else:
        raise Exception("NYI %s" % t)


def toRosetteType(t: Type) -> str:
    if t == Int():
        return "integer?"
    elif t == Bool():
        return "boolean?"
    else:
        raise Exception("NYI: %s" % t)

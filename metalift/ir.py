from abc import abstractmethod
from enum import Enum
from inspect import isclass
import re
import traceback

from llvmlite.binding import TypeRef, ValueRef
from collections import Counter
import typing
from typing import (  # type: ignore
    Any,
    Callable,
    Dict,
    Generic,
    List as pyList,
    Set as pySet,
    TypeVar,
    Union,
    Optional,
    Tuple as pyTuple,
    _GenericAlias,
    cast,
    get_args,
    get_origin,
    cast,
)
from metalift.types import Type, FnT, PointerT


class PrintMode(Enum):
    SMT = 0
    Rosette = 1


ObjectT = typing.Type["Object"]
T = TypeVar("T")

# Helper functions
def is_matrix_type(ty: Union[type, _GenericAlias]) -> bool:
    if isinstance(ty, _GenericAlias):
        return issubclass(get_origin(ty), Matrix)  # type: ignore
    else:
        return issubclass(ty, Matrix)


def get_matrix_element_type(ty: _GenericAlias) -> ObjectT:
    return get_args(ty)[0]  # type: ignore


def is_list_type(ty: Union[type, _GenericAlias]) -> bool:
    if isinstance(ty, _GenericAlias):
        return issubclass(get_origin(ty), List)  # type: ignore
    else:
        return issubclass(ty, List)


def is_nested_list_type(ty: Union[type, _GenericAlias]) -> bool:
    contained_type = get_args(ty)[0]
    return (
        is_list_type(ty)
        and isinstance(contained_type, _GenericAlias)
        and issubclass(get_origin(contained_type), List)  # type: ignore
    )


def get_nested_list_element_type(ty: Union[type, _GenericAlias]) -> ObjectT:
    if not is_nested_list_type(ty):
        raise Exception("expr is not a nested list!")
    contained_type = get_args(ty)[0]
    return get_args(contained_type)[0]  # type: ignore


def get_list_element_type(ty: _GenericAlias) -> ObjectT:
    return get_args(ty)[0]  # type: ignore


def is_set_type(ty: Union[type, _GenericAlias]) -> bool:
    if isinstance(ty, _GenericAlias):
        return issubclass(get_origin(ty), Set)  # type: ignore
    else:
        return issubclass(ty, Set)


def is_tuple_type(ty: Union[type, _GenericAlias]) -> bool:
    if isinstance(ty, _GenericAlias):
        return issubclass(get_origin(ty), Tuple)  # type: ignore
    else:
        return issubclass(ty, Tuple)


def is_primitive_type(ty: Union[type, _GenericAlias]) -> bool:
    return ty == Int or ty == Bool


def is_pointer_type(ty: Union[type, _GenericAlias]) -> bool:
    return not is_primitive_type(ty)


def is_fn_decl_type(ty: Union[type, _GenericAlias]) -> bool:
    if isinstance(ty, _GenericAlias):
        return issubclass(get_origin(ty), Fn)  # type: ignore
    else:
        return issubclass(ty, Fn)


def get_fn_return_type(ty: Union[type, _GenericAlias]) -> ObjectT:
    tuple_types = get_args(ty)[0]
    return get_args(tuple_types)[0]  # type: ignore


def get_fn_args_types(ty: Union[type, _GenericAlias]) -> pyList[ObjectT]:
    tuple_types = get_args(ty)[0]
    return list(get_args(tuple_types)[1:])


class Expr:
    def __init__(self, type: ObjectT, args: Any, metadata: Dict[str, Any] = {}) -> None:
        self.args = args
        self.type = type
        self.metadata = metadata

    # TODO: move into per-type implementations
    def mapArgs(self, f: Callable[["Expr"], "Expr"]) -> "Expr":
        if isinstance(self, Var):
            # TODO(jie)
            return Var(typing.cast(str, f(self.args[0])), self.type)
        elif isinstance(self, Lit):
            return Lit(typing.cast(Union[bool, int, str], f(self.args[0])), self.type)
        elif isinstance(self, Add):
            return Add(*[f(a) for a in self.args])
        elif isinstance(self, Sub):
            return Sub(*[f(a) for a in self.args])
        elif isinstance(self, Mul):
            return Mul(*[f(a) for a in self.args])
        elif isinstance(self, Div):
            return Div(*[f(a) for a in self.args])
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
        elif isinstance(self, TupleExpr):
            return TupleExpr(*[f(a) for a in self.args])
        elif isinstance(self, Let):
            return Let(*[f(a) for a in self.args])
        elif isinstance(self, Lambda):
            return Lambda(self.type.args[0], *[f(a) for a in self.args])  # type: ignore
        elif isinstance(self, Choose):
            return Choose(*[f(a) for a in self.args])
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

    def chooseArbitrarily(self) -> "Expr":
        return self.mapArgs(
            lambda x: x.chooseArbitrarily() if isinstance(x, Expr) else x
        )

    @staticmethod
    def findCommonExprs(
        e: "Expr", cnts: pyList[pyTuple["Expr", int]]
    ) -> pyList[pyTuple["Expr", int]]:
        def expr_index_in_cnts(e: Expr) -> int:
            for i, (existing_expr, _) in enumerate(cnts):
                if Expr.__eq__(e, existing_expr):
                    return i
            return -1

        expr_index = expr_index_in_cnts(e)
        if expr_index == -1:
            cnts.append((e, 1))
            for i in range(len(e.args)):
                if isinstance(e.args[i], Expr):
                    cnts = Expr.findCommonExprs(e.args[i], cnts)
        else:
            _, cnt = cnts[expr_index]
            cnts[expr_index] = (e, cnt + 1)
        return cnts

    @staticmethod
    def replaceExprs(
        e: Union[bool, "Expr", ValueRef, int, str],
        commonExprs: typing.List[Union["Expr", Any]],
        mode: PrintMode,
        skipTop: bool = False,
    ) -> Union["Expr", ValueRef]:
        # skipTop is used to ignore the top-level match when simplifying a common expr
        if all([not Expr.__eq__(e, expr) for expr in commonExprs]) or skipTop:  # type: ignore
            if isinstance(e, Expr):
                newArgs = [Expr.replaceExprs(arg, commonExprs, mode) for arg in e.args]
                if isinstance(e, Object):
                    return Expr.replaceExprs(e.src, commonExprs, mode)
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
                elif isinstance(e, Implies):
                    return Implies(*newArgs)
                elif isinstance(e, Add):
                    return Add(*newArgs)
                elif isinstance(e, Sub):
                    return Sub(*newArgs)
                elif isinstance(e, Mul):
                    return Mul(*newArgs)
                elif isinstance(e, Div):
                    return Div(*newArgs)
                elif isinstance(e, Call):
                    return Call(typing.cast(str, newArgs[0]), e.type, *newArgs[1:])
                elif isinstance(e, Choose):
                    return Choose(*newArgs)
                elif isinstance(e, TupleExpr):
                    return TupleExpr(*newArgs)
                elif isinstance(e, TupleGet):
                    return TupleGet(*newArgs)
                elif isinstance(e, Let):
                    return Let(*newArgs)
                elif isinstance(e, Lambda):
                    return Lambda(e.type.args[0], *newArgs)  # type: ignore
                elif isinstance(e, CallValue):
                    return CallValue(*newArgs)
                else:
                    raise Exception("NYI: %s" % e)
            else:
                return e  # ValueRef or TypeRef
        else:
            assert isinstance(e, Expr)
            if mode == PrintMode.Rosette:
                return Var("(v%d)" % commonExprs.index(e), e.type)
            else:
                return Var("v%d" % commonExprs.index(e), e.type)

    def __repr__(self) -> str:
        fn: Callable[[Union[ValueRef, Var]], Any] = (
            lambda a: a.name if isinstance(a, ValueRef) and a.name != "" else str(a)
        )

        return (
            f"({type(self).__name__}:{get_type_str(self.type)} "
            f'{" ".join(fn(a) for a in self.args)})'
        )

    def codegen(self) -> str:
        fn: Callable[[Union[ValueRef, Var]], Any] = (
            lambda a: a.name if isinstance(a, ValueRef) and a.name != "" else str(a)
        )
        return (
            f"({type(self).__name__}:{get_type_str(self.type)} "
            f'{" ".join(str(a.codegen()) if isinstance(a, Expr) else fn(a) for a in self.args)})'
        )

    def __eq__(self, other: Any) -> bool:
        if isinstance(self, Object) and isinstance(other, Object):
            return Expr.__eq__(self.src, other.src)
        elif isinstance(other, Expr):
            if (
                type(self) != type(other)
                # or self.type.erase() #TODO: add them back
                # != other.type.erase()
                or len(self.args) != len(other.args)
            ):
                return False
            else:
                for a1, a2 in zip(self.args, other.args):
                    if isinstance(a1, Type) and isinstance(a2, Type):
                        if a1 != a2:
                            return False
                        continue
                    elif isinstance(a1, Expr) and isinstance(a2, Expr):
                        if not Expr.__eq__(a1, a2):
                            return False
                        continue
                    elif a1 != a2:
                        return False
                return True
        return NotImplemented

    def __ne__(self, other: Any) -> bool:
        x = self.__eq__(other)
        if x is not NotImplemented:
            return not x
        return NotImplemented

    def __hash__(self) -> int:
        return hash(tuple(sorted({"type": self.type, "args": tuple(self.args)})))

    def toSMT(self) -> str:
        raise NotImplementedError

    def accept(self, v: "Visitor[T]") -> T:
        raise NotImplementedError("not implemented")

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

    @staticmethod
    def get_list_fn(expr: Union["Call", "CallValue"]) -> Optional[str]:
        if isinstance(expr, Call):
            fn_name = expr.name()
        else:
            fn_name = expr.value()  # type: ignore
        if fn_name == "list_get":
            if is_list_type(expr.type):
                return "list-list-ref-noerr"
            elif is_primitive_type(expr.type):
                return "list-ref-noerr"
            else:
                raise Exception(
                    f"list_get not supported on {List[expr.type]} lists yet!"  # type: ignore
                )
        elif fn_name == "list_append":
            if is_list_type(expr.type):
                return "list-list-append"
            elif is_primitive_type(expr.type):
                return "list-append"
            else:
                raise Exception(
                    f"list_append not supported on {List[expr.type]} lists yet!"  # type: ignore
                )
        elif fn_name == "list_empty":
            if is_nested_list_type(expr.type):
                return "list-list-empty"
            elif is_primitive_type(get_list_element_type(expr.type)):
                return "list-empty"
            else:
                raise Exception(f"list_empty not supported on {list_type} lists yet!")  # type: ignore
        elif fn_name == "list_tail":
            list_type = expr.arguments()[0].type
            if is_nested_list_type(list_type):
                return "list-list-tail-noerr"
            elif is_primitive_type(get_list_element_type(list_type)):
                return "list-tail-noerr"
            else:
                raise Exception(f"list_tail not supported on {list_type} lists yet!")
        elif fn_name == "list_length":
            list_type = expr.arguments()[0].type
            if is_nested_list_type(list_type):
                return "list-list-length"
            elif is_primitive_type(get_list_element_type(list_type)):
                return "length"
            else:
                raise Exception(f"list_length not supported on {list_type} lists yet!")
        elif fn_name == "list_take":
            list_type = expr.arguments()[0].type
            if is_nested_list_type(list_type):
                return "list-list-take-noerr"
            elif is_primitive_type(get_list_element_type(list_type)):
                return "list-take-noerr"
            else:
                raise Exception(f"list_take not supported on {list_type} lists yet!")
        elif fn_name == "list_prepend":
            list_type = expr.type
            if is_nested_list_type(list_type):
                return "list-list-prepend"
            elif is_primitive_type(get_list_element_type(list_type)):
                return "list-prepend"
            else:
                raise Exception(
                    f"list_prepend not supported on {List[expr.type]} lists yet!"  # type: ignore
                )
        elif fn_name == "list_eq":
            return "equal?"
        elif fn_name == "list_concat":
            list_type = expr.arguments()[0].type
            if is_primitive_type(get_list_element_type(list_type)):
                return "list-concat"
            raise Exception(f"list_concat not supported on {list_type} lists yet!")
        return None

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
        self, counts: Dict[str, int], new_vars: typing.Set["Var"]
    ) -> "Expr":
        if isinstance(self, Eq):
            replacement_var = Var("useless_equality_%d" % len(new_vars), Bool)
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

        return self.mapArgs(
            lambda a: a.optimizeUselessEquality(counts, new_vars)
            if isinstance(a, Expr)
            else a
        ).simplify()

    # convenience methods
    def __add__(self, other: "Expr") -> "Add":
        if isinstance(self, Add):
            return Add(*self.args, other)
        else:
            return Add(self, other)

    def __sub__(self, other: "Expr") -> "Sub":
        if isinstance(self, Sub):
            return Sub(*self.args, other)
        else:
            return Sub(self, other)

    def __mul__(self, other: "Expr") -> "Mul":
        if isinstance(self, Mul):
            return Mul(*self.args, other)
        else:
            return Mul(self, other)


### START OF IR OBJECTS
ObjectContainedT = Union[ObjectT, _GenericAlias]


def get_type_str(type: Union[Type, ObjectT]) -> str:
    if isinstance(type, Type):
        return str(type)
    else:
        return type.cls_str(get_args(type))  # type: ignore


def toRosetteType(t: ObjectT) -> str:
    if t == Int:
        return "integer?"
    elif t == Bool:
        return "boolean?"
    else:
        raise Exception("NYI: %s" % t)


# TODO(jie): fix the type in the function signature
def parse_type_ref_to_obj(t: TypeRef) -> ObjectT:
    if is_new_object_type(t):
        return t  # type: ignore
    ty_str = str(t)
    if ty_str in {"i32", "i32*"}:
        return Int
    elif ty_str in {"i1", "i8", "i8*"}:
        return Bool
    elif ty_str in {"%struct.list*", "%struct.list**"}:
        # TODO(colin): add generic type support
        # TODO(jie): retire struct.list and use STL?
        return List[Int]
    elif re.match('%"class.std::__1::vector(\.\d+)?"*', ty_str):
        # The \d+ is here is because if we try to parse multiple llvm files that contain types with the same names, then each time after the first time that llvmlite sees this type, it will append a ".{random number}" after the type. For example, the second time we see %"class.std::__1::vector"*, llvmlite will turn it into %"class.std::__1::vector.0"*
        return List[Int]
    elif ty_str in {"%struct.set*"}:
        # TODO jie: how to support different contained types
        return Set[Int]
    elif ty_str in {"%struct.tup*"}:
        return Tuple[typing.Tuple[Int, Int]]
    elif ty_str.startswith("%struct.tup."):
        contained_types = [Int for i in range(int(t[-2]) + 1)]
        return Tuple[typing.Tuple[contained_types]]  # type: ignore
    else:
        raise Exception(f"no type defined for {ty_str}")


def parse_c_or_cpp_type_to_obj(ty_str: str) -> ObjectT:
    if ty_str == "int":
        return Int
    if ty_str == "std::__1::vector<int, std::__1::allocator<int> >":
        return List[Int]
    if (
        ty_str
        == "std::__1::vector<std::__1::vector<int, std::__1::allocator<int> >, std::__1::allocator<std::__1::vector<int, std::__1::allocator<int> > > >"
    ):
        return List[List[Int]]
    raise Exception(f"no type defined for {ty_str}")


def create_object(
    object_type: ObjectT, value: Optional[Union[bool, str, Expr]] = None
) -> "Object":
    if isinstance(object_type, _GenericAlias):
        object_cls = get_origin(object_type)
        contained_types = get_args(object_type)
        return object_cls(*contained_types, value)  # type: ignore
    else:
        return object_type(cast(Expr, value))


def get_object_exprs(*objects: Union["Object", Expr]) -> pyList[Expr]:
    return [get_object_expr(obj) for obj in objects]


def get_object_expr(object: Union["Object", Expr]) -> Expr:
    return object.src if isinstance(object, Object) else object


def is_new_object_type(ty: ObjectContainedT) -> bool:
    if isinstance(ty, _GenericAlias):
        return issubclass(get_origin(ty), Object)  # type: ignore
    return isclass(ty) and issubclass(ty, Object)


def choose(*objects: Union["Object", Expr]) -> "Object":
    if len(objects) == 0:
        raise Exception("Must have at least 1 object to choose from!")
    # Assume that all objects passed in will have the same type, even if not, the call to Choose
    # will handle exception throwing for us.
    object_type = objects[0].type
    choose_expr = Choose(*get_object_exprs(*objects))
    return create_object(object_type, choose_expr)


def ite(
    cond: "Bool",
    then_object: "Object",
    else_object: "Object",
) -> "Object":
    ite_type = then_object.type
    ite_expr = Ite(
        get_object_expr(cond),
        get_object_expr(then_object),
        get_object_expr(else_object),
    )
    return create_object(ite_type, ite_expr)


def implies(e1: "Bool", e2: "Bool") -> "Bool":
    return Bool(Implies(get_object_expr(e1), get_object_expr(e2)))


def call(
    fn_name: str, return_type: ObjectT, *object_args: Union["Object", Expr]
) -> "Object":
    call_expr = Call(fn_name, return_type, *get_object_exprs(*object_args))
    return create_object(return_type, call_expr)


def call_value(fn_decl: "Fn", *object_args: "Object") -> "Object":  # type: ignore
    call_value_expr = CallValue(fn_decl.src, *get_object_exprs(*object_args))
    ret_type = fn_decl.return_type
    return create_object(ret_type, call_value_expr)


def fn_decl(
    fn_name: str,
    return_type: ObjectT,
    body: Union["Object", Expr],
    *object_args: Union["Object", Expr],
) -> "FnDecl":
    fn_decl_expr = FnDecl(
        fn_name, return_type, get_object_expr(body), *get_object_exprs(*object_args)
    )
    return fn_decl_expr


def fn_decl_recursive(
    fn_name: str,
    return_type: ObjectT,
    body: Union["Object", Expr],
    *object_args: Union["Object", Expr],
) -> "FnDeclRecursive":

    fn_decl_recursive_expr = FnDeclRecursive(
        fn_name, return_type, get_object_expr(body), *get_object_exprs(*object_args)
    )
    return fn_decl_recursive_expr


def make_tuple(*objects: Union["Object", Expr]) -> "Tuple":  # type: ignore
    obj_types = tuple([obj.type for obj in objects])
    return Tuple(obj_types, TupleExpr(*get_object_exprs(*objects)))  # type: ignore


def make_tuple_type(*containedT: Union[type, _GenericAlias]) -> typing.Type["Tuple"]:  # type: ignore
    return Tuple[typing.Tuple[containedT]]  # type: ignore


def make_fn_type(*containedT: ObjectT) -> typing.Type["Fn"]:  # type: ignore
    return Fn[typing.Tuple[containedT]]  # type: ignore


class Object:
    src: Expr

    def __init__(self, src: Expr) -> None:
        self.src = src
        self.__class__.__hash__ = Object.__hash__  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return self.src.toRosette(writeChoicesTo)

    def var_name(self) -> str:
        if not isinstance(self.src, Var):
            raise Exception("source is not a variable")
        return self.src.name()

    def __repr__(self) -> str:
        return repr(self.src)

    def codegen(self) -> str:
        return self.src.codegen()

    def __hash__(self) -> int:
        return hash(self.src)

    def __eq__(self, other: Any) -> bool:
        if not isinstance(other, Object):
            return False
        return self.src == other.src

    @staticmethod
    def default_value() -> "Object":
        raise NotImplementedError()

    @property
    def type(self) -> ObjectT:
        raise NotImplementedError()

    @staticmethod
    def toSMTType(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        raise NotImplementedError()

    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        raise NotImplementedError()


class Bool(Object):
    def __init__(self, value: Optional[Union[bool, str, Expr]] = None) -> None:
        src: Expr
        if value is None:
            src = Var("v", Bool)
        elif isinstance(value, bool):
            src = BoolLit(value)
        elif isinstance(value, Expr):
            if value.type != Bool:
                raise TypeError(f"Cannot create Bool from {value.type}")
            src = value
        elif isinstance(value, str):
            src = Var(value, Bool)
        else:
            raise TypeError(f"Cannot create Bool from {value}")

        Object.__init__(self, src)

    @property
    def type(self) -> typing.Type["Bool"]:
        return Bool

    @staticmethod
    def default_value() -> "Bool":
        return Bool(False)

    # python doesn't have hooks for and, or, not
    def And(self, *args: Union["Bool", bool]) -> "Bool":
        if len(args) == 0:
            raise Exception(f"Arg list must be non-empty: {args}")
        return Bool(And(*get_object_exprs(self, *args)))  # type: ignore

    def Or(self, *args: Union["Bool", bool]) -> "Bool":
        if len(args) == 0:
            raise Exception(f"Arg list must be non-empty: {args}")
        return Bool(Or(*get_object_exprs(self, *args)))  # type: ignore

    def Not(self) -> "Bool":
        return Bool(Not(self.src))

    def __eq__(self, other: Union["Bool", bool]) -> "Bool":  # type: ignore
        if isinstance(other, bool):
            other = Bool(other)
        return Bool(Eq(self.src, other.src))

    def __ne__(self, other: Union["Bool", bool]) -> "Bool":  # type: ignore
        if isinstance(other, bool):
            other = Bool(other)
        return Bool(Not(Eq(self.src, other.src)))

    def __repr__(self) -> str:
        return f"{self.src}"

    @staticmethod
    def toSMTType(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        return "Bool"

    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        return "Bool"


class Int(Object):
    def __init__(self, value: Optional[Union[int, str, Expr]] = None) -> None:
        src: Expr
        if value is None:
            src = Var("v", Int)
        elif isinstance(value, int):
            src = IntLit(value)
        elif isinstance(value, Expr):
            if value.type != Int:
                raise TypeError(f"Cannot create Int from {value.type}")
            src = value
        elif isinstance(value, str):
            src = Var(value, Int)
        else:
            raise TypeError(f"Cannot create Int from {value}")

        Object.__init__(self, src)

    @property
    def type(self) -> typing.Type["Int"]:
        return Int

    @staticmethod
    def default_value() -> "Int":
        return Int(0)

    def binary_op(
        self, other: Union["Int", int], op: Callable[[Expr, Expr], Expr]
    ) -> "Int":
        if isinstance(other, int):
            other = Int(other)
        if isinstance(other, Int):
            return Int(op(self.src, other.src))
        raise TypeError(f"Cannot call {op} on Int {self} and {other}")

    # arithmetic operators
    def __add__(self, other: Union["Int", int]) -> "Int":
        return self.binary_op(other, Add)

    def __sub__(self, other: Union["Int", int]) -> "Int":
        return self.binary_op(other, Sub)

    def __mul__(self, other: Union["Int", int]) -> "Int":
        return self.binary_op(other, Mul)

    def __floordiv__(self, other: Union["Int", int]) -> "Int":
        return self.binary_op(other, Div)

    def __radd__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(other) + self
        else:
            return other + self

    def __rsub__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(other) - self
        else:
            return other - self

    def __rmul__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(other) * self
        else:
            return other * self

    def __rfloordiv__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(other) // self
        else:
            return other // self

    # logical comparison operators
    def __eq__(self, other: Union["Int", int]) -> Bool:  # type: ignore
        if isinstance(other, int):
            other = Int(other)
        return Bool(Eq(self.src, other.src))

    def __ne__(self, other: Union["Int", int]) -> Bool:  # type: ignore
        if isinstance(other, int):
            other = Int(other)
        return Bool(Not(Eq(self.src, other.src)))

    def __ge__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(other)
        return Bool(Ge(self.src, other.src))

    def __gt__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(other)
        return Bool(Gt(self.src, other.src))

    def __lt__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(other)
        return Bool(Lt(self.src, other.src))

    def __le__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(other)
        return Bool(Le(self.src, other.src))

    @staticmethod
    def toSMTType(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        return "Int"

    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        return "Int"


class List(Generic[T], Object):
    containedT: ObjectContainedT

    def __init__(
        self,
        containedT: ObjectContainedT = Int,
        value: Optional[Union[Expr, str]] = None,
    ) -> None:
        full_type = List[containedT]  # type: ignore
        src: Expr
        if value is None:  # a symbolic variable
            src = Var("v", full_type)
        elif isinstance(value, Expr):
            src = value
        elif isinstance(value, str):
            src = Var(value, full_type)
        else:
            raise TypeError(f"Cannot create List from {value}")
        self.containedT = containedT
        Object.__init__(self, src)

    @property
    def type(self) -> typing.Type["List"]:  # type: ignore
        return List[self.containedT]  # type: ignore

    @staticmethod
    def empty(containedT: ObjectContainedT) -> "List":  # type: ignore
        return List(containedT, Call("list_empty", List[containedT]))  # type: ignore

    @staticmethod
    def default_value() -> "List[Int]":
        return List.empty(Int)

    def __len__(self) -> int:
        raise NotImplementedError("len must return an int, call len() instead")

    def len(self) -> Int:
        return Int(Call("list_length", Int, self.src))

    def __getitem__(self, index: Union[Int, int, slice]) -> Object:
        if isinstance(index, int):
            index = Int(index)
        if isinstance(index, slice):
            (start, stop, step) = (index.start, index.stop, index.step)
            if stop is None and step is None:
                if isinstance(start, int):
                    start = Int(start)
                return call("list_tail", List[self.containedT], self, start)  # type: ignore
            elif start is None and step is None:
                if isinstance(stop, int):
                    stop = Int(stop)
                return call("list_take", List[self.containedT], self, stop)  # type: ignore
            else:
                raise NotImplementedError(
                    f"Slices with both start and stop indices specified are not implemented: {index}"
                )

        return call("list_get", self.containedT, self, index)

    def __setitem__(self, index: Union[Int, int], value: Object) -> None:
        if isinstance(index, int):
            index = Int(index)
        if value.type != self.containedT:
            raise TypeError(
                f"Trying to set list element of type: {value.type} to list containing: {self.containedT}"
            )
        self.src = Call("list_set", self.type, self.src, index.src, value.src)

    # in place append
    def append(self, value: Object) -> "List":  # type: ignore
        if value.type != self.containedT:
            raise TypeError(
                f"Trying to append element of type: {value.type} to list containing: {self.containedT}"
            )

        self.src = call("list_append", self.type, self, value).src
        return self

    # in place prepend
    def prepend(self, value: Object) -> "List":  # type: ignore
        if value.type != self.containedT:
            raise TypeError(
                f"Trying to append element of type: {value.type} to list containing: {self.containedT}"
            )

        self.src = call("list_prepend", self.type, value, self).src
        return self

    # list concat that returns a new list
    def __add__(self, other: "List") -> "List":  # type: ignore
        if self.type != other.type:
            raise TypeError(
                f"can't add lists of different types: {self.type} and {other.type}"
            )
        return List(
            self.containedT, Call("list_concat", self.type, self.src, other.src)
        )

    def __eq__(self, other: "List") -> Bool:  # type: ignore
        if other is None or self.type != other.type:
            return Bool(False)
        else:
            return cast(Bool, call("list_eq", Bool, self, other))

    def __repr__(self) -> str:
        return f"{self.src}"

    @staticmethod
    def toSMTType(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        contained_type = type_args[0]
        if isinstance(contained_type, _GenericAlias):
            return f"(MLList {get_origin(contained_type).toSMTType(get_args(contained_type))})"  # type: ignore
        else:
            return f"(MLList {contained_type.toSMTType()})"

    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        contained_type = type_args[0]
        if isinstance(contained_type, _GenericAlias):
            return f"List {get_origin(contained_type).cls_str(get_args(contained_type))}"  # type: ignore
        else:
            return f"List {contained_type.cls_str()}"


class Matrix(Generic[T], Object):
    containedT: ObjectContainedT

    def __init__(
        self,
        containedT: ObjectContainedT = Int,
        value: Optional[Union[Expr, str]] = None,
    ) -> None:
        full_type = List[List[containedT]]  # type: ignore
        src: Expr
        if value is None:  # a symbolic variable
            src = Var("v", full_type)
        elif isinstance(value, Expr):
            src = value
        elif isinstance(value, str):
            src = Var(value, full_type)
        else:
            raise TypeError(f"Cannot create List from {value}")
        self.containedT = List[containedT]  # type: ignore
        Object.__init__(self, src)

    @property
    def type(self) -> typing.Type["List"]:  # type: ignore
        return List[self.containedT]  # type: ignore

    @staticmethod
    def empty(containedT: ObjectContainedT) -> "List":  # type: ignore
        return List(List[containedT], Call("list_empty", List[List[containedT]]))  # type: ignore

    @staticmethod
    def default_value() -> "List[List[Int]]":
        return Matrix.empty(Int)

    def __len__(self) -> int:
        raise NotImplementedError("len must return an int, call len() instead")

    def len(self) -> Int:
        return Int(Call("list_length", Int, self.src))

    def __getitem__(self, index: Union[Int, int, slice]) -> Object:
        if isinstance(index, int):
            index = Int(index)
        if isinstance(index, slice):
            (start, stop, step) = (index.start, index.stop, index.step)
            if stop is None and step is None:
                if isinstance(start, int):
                    start = Int(start)
                return call("list_tail", List[self.containedT], self, start)  # type: ignore
            elif start is None and step is None:
                if isinstance(stop, int):
                    stop = Int(stop)
                return call("list_take", List[self.containedT], self, stop)  # type: ignore
            else:
                raise NotImplementedError(
                    f"Slices with both start and stop indices specified are not implemented: {index}"
                )

        return call("list_get", self.containedT, self, index)

    def __setitem__(self, index: Union[Int, int], value: Object) -> None:
        if isinstance(index, int):
            index = Int(index)
        if value.type != self.containedT:
            raise TypeError(
                f"Trying to set list element of type: {value.type} to list containing: {self.containedT}"
            )
        self.src = Call("list_set", self.type, self.src, index.src, value.src)

    # in place append
    def append(self, value: Object) -> "Matrix":  # type: ignore
        if value.type != self.containedT:
            raise TypeError(
                f"Trying to append element of type: {value.type} to list containing: {self.containedT}"
            )

        self.src = call("list_append", self.type, self, value).src
        return self

    # in place prepend
    def prepend(self, value: Object) -> "Matrix":  # type: ignore
        if value.type != self.containedT:
            raise TypeError(
                f"Trying to append element of type: {value.type} to list containing: {self.containedT}"
            )

        self.src = call("list_prepend", self.type, value, self).src
        return self

    # list concat that returns a new list
    def __add__(self, other: "Matrix") -> "List":  # type: ignore
        if self.type != other.type:
            raise TypeError(
                f"can't add lists of different types: {self.type} and {other.type}"
            )
        return List(List[self.containedT], Call("list_concat", self.type, self.src, other.src))  # type: ignore

    def __eq__(self, other: "Matrix") -> Bool:  # type: ignore
        if other is None or self.type != other.type:
            return Bool(False)
        else:
            return cast(Bool, call("list_eq", Bool, self, other))

    def __repr__(self) -> str:
        return f"{self.src}"

    @staticmethod
    def toSMTType(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        contained_type = type_args[0]
        if isinstance(contained_type, _GenericAlias):
            return f"(MLList {get_origin(contained_type).toSMTType(get_args(contained_type))})"  # type: ignore
        else:
            return f"(MLList {contained_type.toSMTType()})"

    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        contained_type = type_args[0]
        if isinstance(contained_type, _GenericAlias):
            return f"List {get_origin(contained_type).cls_str(get_args(contained_type))}"  # type: ignore
        else:
            return f"List {contained_type.cls_str()}"


class Set(Generic[T], Object):
    def __init__(
        self,
        containedT: Union[type, _GenericAlias] = Int,
        value: Optional[Union[Expr, str]] = None,
    ) -> None:
        src: Expr
        full_type = Set[containedT]  # type: ignore
        if value is None:
            src = Var("v", full_type)
        elif isinstance(value, Expr):
            src = value
        elif isinstance(value, str):
            src = Var(value, full_type)
        else:
            raise TypeError(f"Cannot create Set from {value}")
        self.containedT = containedT
        Object.__init__(self, src)

    @property
    def type(self) -> typing.Type["Set"]:  # type: ignore
        return Set[self.containedT]  # type: ignore

    @staticmethod
    def default_value() -> "Set[Int]":
        return Set(Int)

    def add(self, value: Object) -> "Set":  # type: ignore
        if value.type != self.containedT:
            raise TypeError(
                f"Trying to add element of type: {value.type} to set containing: {self.containedT}"
            )
        return call("set-insert", self.type, value, self)  # type: ignore

    def remove(self, item: Object) -> "Set":  # type: ignore
        if type(item) != self.containedT:
            raise TypeError(
                f"Trying to remove element of type: {type(item)} from set containing: {self.containedT}"
            )
        singleton_s = Set.singleton(item)
        return call("set-minus", self.type, self, singleton_s)  # type: ignore

    @staticmethod
    def singleton(item: Object) -> "Set":  # type: ignore
        return call("set-singleton", Set[type(item)], item)  # type: ignore

    def union(self, s: "Set") -> "Set":  # type: ignore
        if self.type != s.type:
            raise TypeError(
                f"Can't union two sets with type {self.type} and type {s.type}"
            )
        expr = Call("set-union", self.type, self.src, s.src)
        return Set(self.containedT, expr)

    def difference(self, s: "Set") -> "Set":  # type: ignore
        if self.type != s.type:
            raise TypeError(
                f"Can't take the difference of two sets with type {self.type} and type {s.type}"
            )
        return call("set-minus", self.type, self, s)  # type: ignore

    def __contains__(self, value: Object) -> Bool:
        if value.type != self.containedT:
            return Bool(False)
        return cast(Bool, call("set-pointer_varsber", Bool, self, value))

    def __eq__(self, s: "Set") -> Bool:  # type: ignore
        return Bool(Eq(self.src, s.src))
        # return cast(Bool, call("set-eq", Bool, self, s))

    @staticmethod
    def empty(containedT: ObjectContainedT) -> "Set":  # type: ignore
        return Set(containedT, Call("set-create", Set[containedT]))  # type: ignore

    @staticmethod
    def toSMTType(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        return Set.cls_str(type_args)

    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        contained_type = type_args[0]
        if isinstance(contained_type, _GenericAlias):
            return f"(Set {get_origin(contained_type).toSMTType(get_args(contained_type))})"  # type: ignore # this would call List.toSMTType(Int) for instance
        else:
            return f"(Set {contained_type.toSMTType()})"


TupleContainedT = TypeVar("TupleContainedT")


class Tuple(Generic[TupleContainedT], Object):
    def __init__(
        self,
        containedT: typing.Tuple[Union[type, _GenericAlias]],
        value: Optional[Union[Expr, str]] = None,
    ) -> None:
        full_type = Tuple[typing.Tuple[containedT]]  # type: ignore
        src: Expr
        if value is None:  # a symbolic variable
            src = Var("v", full_type)
        elif isinstance(value, Expr):
            src = value
        elif isinstance(value, str):
            src = Var(value, full_type)
        else:
            raise TypeError(f"Cannot create Tuple from {value}")
        self.containedT = containedT
        Object.__init__(self, src)

    def __getitem__(self, index: Union[Int, int]) -> Object:
        if isinstance(index, int):  # promote to Int
            index = Int(index)

        if isinstance(index, Int):
            index_lit = index.src.val()  # type: ignore
            item_type = self.containedT[index_lit]
            if issubclass(item_type, Object):
                # TODO(jie) create a function to wrap objects around expession
                return call("tupleGet", item_type, self, index)
            else:
                raise Exception(
                    "Only primitive object types inside tuples are supported!"
                )
        if isinstance(index, slice):
            raise Exception("slicing operation not supported on tuples!")

    @property
    def length(self) -> int:
        return len(self.containedT)

    @staticmethod
    def default_value() -> "Tuple[typing.Tuple[Int, Int]]":
        return Tuple((Int, Int), None)  # type: ignore

    @staticmethod
    def toSMTType(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        containedT = get_args(type_args[0])
        tuple_length = len(containedT)
        contained_str_list = []
        for contain in containedT:
            if isinstance(contain, _GenericAlias):
                containedT_str = get_origin(contain).toSMTType(get_args(contain))  # type: ignore
            else:
                containedT_str = contain.toSMTType()
            contained_str_list.append(containedT_str)
        return f"(Tuple{tuple_length} {' '.join(contained_str_list)})"  # this would call List.toSMTType(Int) for instance

    # TODO(jie): handle contained type
    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        contained_type_strs: pyList[str] = []
        for contained_type in get_args(type_args[0]):
            if isinstance(contained_type, _GenericAlias):
                contained_type_str = get_origin(contained_type).toSMTType(  # type: ignore
                    get_args(contained_type)
                )
            else:
                contained_type_str = contained_type.toSMTType()
            contained_type_strs.append(contained_type_str)
        return f"Tuple {' '.join(contained_type_strs)}"


FnContainedT = TypeVar("FnContainedT")


class Fn(Generic[FnContainedT], Object):
    def __init__(
        self,
        containedT: typing.Tuple[Union[type, _GenericAlias]],
        value: Optional[Union["FnDeclRecursive", "FnDecl", str]] = None,
    ) -> None:
        full_type = Fn[typing.Tuple[containedT]]  # type: ignore
        self.return_type = containedT[0]
        self.argument_types = containedT[1:]
        src: Expr
        if value is None:  # a symbolic variable
            src = Var("v", full_type)
        elif isinstance(value, FnDecl) or isinstance(value, FnDeclRecursive):
            src = value
        elif isinstance(value, str):
            src = Var(value, full_type)
        else:
            raise TypeError(f"Cannot create Fn from {value}")
        Object.__init__(self, src)

    @property
    def name(self) -> str:
        if isinstance(self.src, FnDecl) or isinstance(self.src, FnDeclRecursive):
            return self.src.name()
        elif isinstance(self.src, Var):
            return self.src.name()
        raise Exception("Unsupported source type for function objects!")

    @staticmethod
    def cls_str(type_args: pyTuple[ObjectContainedT] = ()) -> str:  # type: ignore
        contained_type_strs: pyList[str] = []
        contained_types = get_args(get_args(type_args[0]))
        for contained_type in contained_types:
            if isinstance(contained_type, _GenericAlias):
                contained_type_str = get_origin(contained_type).toSMTType(  # type: ignore
                    get_args(contained_type)
                )
            else:
                contained_type_str = contained_type.toSMTType()
            contained_type_strs.append(contained_type_str)
        return f"Function {' '.join(contained_type_strs)}"


### END OF IR OBJECTS


class Var(Expr):
    def __init__(self, name: str, ty: ObjectT) -> None:
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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Var(self)


# used in defining grammars
class NonTerm(Var):
    currentNum = 0  # current non terminal number

    def __init__(self, t: ObjectT, isStart: bool = False, name: str = "") -> None:
        if name == "":
            name = f"nonTerm{NonTerm.currentNum}"
            NonTerm.currentNum = NonTerm.currentNum + 1
        Var.__init__(self, name, t)
        self.isStart = isStart

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_NonTerm(self)


class Pointer(Expr):
    def __init__(self, val: Expr) -> None:
        Expr.__init__(self, PointerT(val.type), [val])  # type: ignore

    @property
    def value(self) -> Expr:
        return self.args[0]  # type: ignore

    def set_value(self, value: Expr) -> None:
        self.args[0] = value


class Lit(Expr):
    def __init__(self, val: Union[bool, int, str], ty: ObjectT) -> None:
        Expr.__init__(self, ty, [val])

    def val(self) -> Union[bool, int, str]:
        return self.args[0]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        if self.type == Bool:
            return "true" if self.args[0] else "false"
        else:
            return str(self.args[0])

    def toSMT(self) -> str:
        if self.type == Bool:
            return "true" if self.args[0] else "false"
        else:
            return str(self.args[0])

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Lit(self)


class ObjectExpr(Expr):
    def __init__(self, ty: Type) -> None:
        Expr.__init__(self, ty, {})  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        raise Exception("NYI")

    def toSMT(self) -> str:
        raise Exception("NYI")

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Object(self)


def IntLit(val: int) -> Expr:
    return Lit(val, Int)


def EnumIntLit(val: int) -> Expr:
    return Lit(val, Int)
    # TODO(colin): bring EnumBack
    # return Lit(val, EnumInt())


def BoolLit(val: bool) -> Expr:
    return Lit(val, Bool)


class Add(Expr):
    RosetteName = SMTName = "+"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        for arg in args:
            if arg.type != args[0].type:
                raise Exception(f"Args types not equal: {arg.type} and {args[0].type}")
        Expr.__init__(self, Int, args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Add(self)


class Sub(Expr):
    RosetteName = SMTName = "-"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        for arg in args:
            if get_type_str(arg.type) != get_type_str(args[0].type):
                raise Exception(
                    f"Args types not equal: {get_type_str(arg.type)} and {get_type_str(args[0].type)}"
                )
        Expr.__init__(self, Int, args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Sub(self)


class Mul(Expr):
    RosetteName = SMTName = "*"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        for arg in args:
            if get_type_str(arg.type) != get_type_str(args[0].type):
                raise Exception(
                    f"Args types not equal: {get_type_str(arg.type)} and {get_type_str(args[0].type)}"
                )
        Expr.__init__(self, Int, args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Mul(self)


class Div(Expr):
    RosetteName = "quotient"
    SMTName = "div"

    def __init__(self, *args: Expr) -> None:
        if len(args) != 2:
            raise Exception(f"Must exactly have two arguments: {args}")
        for arg in args:
            if get_type_str(arg.type) != get_type_str(args[0].type):
                raise Exception(
                    f"Args types not equal: {get_type_str(arg.type)} and {get_type_str(args[0].type)}"
                )
        Expr.__init__(self, Int, args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Div(self)


class Eq(Expr):
    RosetteName = "equal?"
    SMTName = "="

    def __init__(self, e1: Expr, e2: Expr) -> None:
        # if not (e1.type.erase() == e2.type.erase()): TODO: add them back
        #     raise Exception(
        #         f"Cannot compare values of different types: {e1}: {e1.type.erase()} and {e2}: {e2.type.erase()}"
        #     )
        Expr.__init__(self, Bool, [e1, e2])

    def e1(self) -> Expr:
        return self.args[0]  # type: ignore

    def e2(self) -> Expr:
        return self.args[1]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        if is_set_type(self.e1().type):
            name = "set-eq"
        else:
            name = self.RosetteName
        return Expr.toRosetteSimple(self, name)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Eq(self)


class Lt(Expr):
    RosetteName = SMTName = "<"

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (get_type_str(e1.type) == get_type_str(e2.type)):
            raise Exception(
                f"Cannot compare values of different types: {e1}: {get_type_str(e1.type)} and {e2}: {get_type_str(e2.type)}"
            )
        Expr.__init__(self, Bool, [e1, e2])

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Lt(self)


class Le(Expr):
    RosetteName = SMTName = "<="

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (get_type_str(e1.type) == get_type_str(e2.type)):
            raise Exception(
                f"Cannot compare values of different types: {e1}: {get_type_str(e1.type)} and {e2}: {get_type_str(e2.type)}"
            )
        Expr.__init__(self, Bool, [e1, e2])

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Le(self)


class Gt(Expr):
    RosetteName = SMTName = ">"

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (get_type_str(e1.type) == get_type_str(e2.type)):
            raise Exception(
                f"Cannot compare values of different types: {e1}: {get_type_str(e1.type)} and {e2}: {get_type_str(e2.type)}"
            )
        Expr.__init__(self, Bool, [e1, e2])

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Gt(self)


class Ge(Expr):
    RosetteName = SMTName = ">="

    def __init__(self, e1: Expr, e2: Expr) -> None:
        if not (get_type_str(e1.type) == get_type_str(e2.type)):
            raise Exception(
                f"Cannot compare values of different types: {e1}: {get_type_str(e1.type)} and {e2}: {get_type_str(e2.type)}"
            )
        Expr.__init__(self, Bool, [e1, e2])

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Ge(self)


class And(Expr):
    RosetteName = "&&"  # racket "and" short circuits!
    SMTName = "and"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        if not all(map(lambda e: e.type == Bool, args)):
            # TODO(jie) how to check this type?
            raise Exception(f"Cannot apply AND to values of type {args}")
        Expr.__init__(self, Bool, args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_And(self)


class Or(Expr):
    # XXX we should use || for rosette to avoid short circuiting
    RosetteName = SMTName = "or"

    def __init__(self, *args: Expr) -> None:
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        if not all(map(lambda e: e.type == Bool, args)):
            raise Exception(
                f"Cannot apply OR to values of type {map(lambda e: e.type, args)}"
            )
        Expr.__init__(self, Bool, args)

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Or(self)


class Not(Expr):
    RosetteName = "!"
    SMTName = "not"

    def __init__(self, e: Expr) -> None:
        if e.type != Bool:
            raise Exception(f"Cannot apply NOT to value of type {e.type}")
        Expr.__init__(self, Bool, [e])

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Not(self)


class Implies(Expr):
    RosetteName = SMTName = "=>"

    def __init__(self, e1: Union[Expr, "MLInst"], e2: Union[Expr, "MLInst"]) -> None:
        if e1.type != Bool:  # type: ignore
            raise Exception(f"Cannot apply IMPLIES to value of type {e1.type}")  # type: ignore
        if e2.type != Bool:  # type: ignore
            raise Exception(f"Cannot apply IMPLIES to value of type {e2.type}")  # type: ignore
        Expr.__init__(self, Bool, [e1, e2])

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Implies(self)


class Ite(Expr):
    RosetteName = "if"
    SMTName = "ite"

    def __init__(self, c: Expr, e1: Expr, e2: Expr) -> None:
        if c.type != Bool:
            raise Exception(
                f"ITE condition must be Boolean and not value of type {c.type}"
            )
        if get_type_str(e1.type) != get_type_str(e2.type):
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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Ite(self)


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
        let_expr = (
            self.args[1].name
            if isinstance(self.args[1], ValueRef) and self.args[1].name != ""
            else self.args[1]
            if isinstance(self.args[1], str)
            else self.args[1].toRosette()
        )

        return f"(let ([{self.args[0].toRosette()} {let_expr}]) {self.args[2].toRosette()})"

    def toSMT(self) -> str:
        return "(let ((%s %s)) %s)" % (
            self.args[0].toSMT(),
            self.args[1].toSMT(),
            self.args[2].toSMT(),
        )

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Let(self)


class Call(Expr):
    def __init__(self, name: str, returnT: ObjectT, *arguments: Expr) -> None:
        Expr.__init__(self, returnT, [name, *arguments])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[1:]  # type: ignore

    def __repr__(self) -> str:
        fn: Callable[[Union[ValueRef, Var]], Any] = (
            lambda a: a.name if isinstance(a, ValueRef) and a.name != "" else str(a)
        )
        return f"({self.args[0]}:{get_type_str(self.type)} {' '.join(fn(a) for a in self.args[1:])})"

    def codegen(self) -> str:
        fn: Callable[[Union[ValueRef, Var]], Any] = (
            lambda a: a.name if isinstance(a, ValueRef) and a.name != "" else str(a)
        )
        return f"({self.args[0]}:{get_type_str(self.type)} {' '.join(str(a.codegen()) if isinstance(a, Expr) else fn(a) for a in self.args[1:])})"

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
                callStr = f"({Expr.get_list_fn(self) or self.args[0]} "
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
            return f"(as set.empty {self.type.toSMTType(get_args(self.type))})"  # type: ignore

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
                index = self.args[idx + 2].args[0]
                if isinstance(self.args[idx + 1], TupleExpr):
                    retVal.append(
                        "tuple%d_get%d"
                        % (
                            len(self.args[idx + 1].args),
                            index,
                        )
                    )
                elif (
                    len(self.args[idx + 1].args) > 0
                    and self.args[idx + 1].args[0] == "make-tuple"
                ):
                    retVal.append(
                        "tuple%d_get%d"
                        % (
                            len(self.args[idx + 1].args) - 1,
                            index,
                        )
                    )
                elif isinstance(self.args[idx + 1], Tuple):
                    retVal.append(f"tuple{self.args[idx + 1].length}_get{index}")
                elif (
                    isinstance(self.args[idx + 1], Var)
                    and get_origin(self.args[idx + 1].type) == Tuple
                ):
                    length = len(get_args(get_args(self.args[idx + 1].type)[0]))
                    retVal.append(f"tuple{length}_get{index}")
                else:
                    # HACK: if function argument is a tuple, count I's in the mangled names of args to get number of elements in tuple
                    freq: typing.Counter[str] = Counter(
                        self.args[idx + 1].args[0].split("_")[1]
                    )
                    retVal.append("tuple%d_get%d" % (freq["i"], index))
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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Call(self)


class CallValue(Expr):
    def __init__(self, value: Expr, *arguments: Expr) -> None:
        if not is_fn_decl_type(value.type):
            raise Exception(f"value must be fn decl type for call value")
        Expr.__init__(self, get_fn_return_type(value.type), [value, *arguments])

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
                callStr = f"({Expr.get_list_fn(self) or self.args[0]} "
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
            return f"(as set.empty {self.type.toSMT()})"  # type: ignore

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_CallValue(self)


class Assert(Expr):
    RosetteName = SMTName = "assert"

    def __init__(self, e: Expr) -> None:
        Expr.__init__(self, Bool, [e])

    def e(self) -> Expr:
        return self.args[0]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return Expr.toRosetteSimple(self, self.RosetteName)

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Assert(self)


class Constraint(Expr):
    SMTName = "constraint"

    def __init__(self, e: Expr) -> None:
        Expr.__init__(self, Bool, [e])

    def e(self) -> Expr:
        return self.args[0]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        raise Exception("NYI")

    def toSMT(self) -> str:
        return Expr.toSMTSimple(self, self.SMTName)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Constraint(self)


## tuple functions
class TupleExpr(Expr):
    def __init__(self, *args: Expr) -> None:
        tuple_type = make_tuple_type(*[a.type for a in args])
        Expr.__init__(self, tuple_type, args)

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_TupleExpr(self)


class TupleGet(Expr):
    def __init__(self, t: Expr, i: Expr) -> None:
        # TODO: type.args no longer exist. need proper fix
        Expr.__init__(self, t.type.args[i.args[0]], [t, i])  # type: ignore

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_TupleGet(self)


class Axiom(Expr):
    def __init__(self, e: Expr, *vars: Expr) -> None:
        Expr.__init__(self, Bool, [e, *vars])

    def e(self) -> Expr:
        return self.args[0]  # type: ignore

    def vars(self) -> typing.List[Expr]:
        return self.args[1:]  # type: ignore

    def toRosette(
        self,
        writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None,
        is_uninterp: bool = True,
    ) -> str:
        return ""  # axioms are only for verification

    def toSMT(self) -> str:
        vs = [
            "(%s %s)" % (a.args[0], a.type.toSMTType(get_args(a.type)))  # type: ignore
            for a in self.vars()
        ]
        return "(assert (forall ( %s ) %s ))" % (" ".join(vs), self.args[0].toSMT())

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Axiom(self)


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
        cnts = Expr.findCommonExprs(self.args[1], [])
        commonExprs = list(
            filter(
                lambda k: isinstance(k, Choose),
                [expr_cnt_tup[0] for expr_cnt_tup in cnts],
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
        cnts = Expr.findCommonExprs(self.args[1], [])
        commonExprs = list(
            filter(
                lambda k: isinstance(k, Choose),
                [expr_cnt_tup[0] for expr_cnt_tup in cnts],
            )
        )
        rewritten = Expr.replaceExprs(self.args[1], commonExprs, PrintMode.SMT)

        # rewrite common exprs to use each other
        commonExprs = [
            Expr.replaceExprs(e, commonExprs, PrintMode.SMT, skipTop=True)
            for e in commonExprs
        ]

        return_type = self.type.toSMTType(get_args(self.type))  # type: ignore
        common_exprs_types: pyList[str] = []
        for expr in commonExprs:
            expr_type = parse_type_ref_to_obj(expr.type)
            expr_smt_type = expr_type.toSMTType(get_args(expr_type))  # type: ignore
            common_exprs_types.append(expr_smt_type)

        decls = "((rv %s) %s)" % (
            return_type,
            " ".join(
                "(%s %s)" % ("v%d" % i, smt_type)
                for i, smt_type in enumerate(common_exprs_types)
            ),
        )
        defs = "(rv %s %s)\n" % (
            return_type,
            rewritten.toSMT()
            if isinstance(rewritten, Choose)
            else "(%s)" % rewritten.toSMT(),
        )
        defs = defs + "\n".join(
            "(%s %s %s)"
            % (
                "v%d" % i,
                common_exprs_types[i],
                e.toSMT() if isinstance(e, Choose) else f"({e.toSMT()})",
            )
            for i, e in enumerate(commonExprs)
        )

        body = decls + "\n" + "(" + defs + ")"

        declarations = []
        for a in self.args[2:]:
            if isinstance(a, ValueRef):
                declarations.append((a.name, a.type))
            else:
                declarations.append((a.args[0], a.type))

        args = " ".join(
            "(%s %s)" % (d[0], d[1].toSMTType(get_args(d[1]))) for d in declarations
        )
        return "(synth-fun %s (%s) %s\n%s)" % (
            self.args[0],
            args,
            return_type,
            body,
        )

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Synth(self)


class Choose(Expr):
    def __init__(self, *args: Expr) -> None:
        if not all(a.type == args[0].type for a in args):
            raise Exception(
                "Choose args are of different types: %s"
                % " ".join(str(a.type) for a in args)
            )
        Expr.__init__(self, args[0].type, args)

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args  # type: ignore

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
        retVal = []

        for a in self.args:
            if isinstance(a, ValueRef) and a.name != "":
                retVal.append(a.name)
            elif isinstance(a, str):
                retVal.append(str(a))
            else:
                retVal.append(a.toSMT())

        retT = "(" + " ".join(retVal) + ")"

        return retT

    def chooseArbitrarily(self) -> "Expr":
        return self.args[0]  # type: ignore

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Choose(self)


class FnDeclRecursive(Expr):
    def __init__(
        self,
        name: str,
        returnT: ObjectT,
        body: Union[Expr, str],
        *args: Expr,
    ) -> None:
        self.return_type = returnT
        arg_types = tuple([arg.type for arg in args])
        fn_type = make_fn_type(returnT, *arg_types)
        Expr.__init__(self, fn_type, [name, body, *args])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def returnT(self) -> ObjectT:
        return self.return_type

    def body(self) -> Union[Expr, str]:
        return self.args[1]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[2:]  # type: ignore

    def toRosette(
        self,
        writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None,
        is_uninterp: bool = False,
    ) -> str:
        if self.args[1] is None and is_uninterp:  # uninterpreted function
            args_type = " ".join(["%s" % toRosetteType(a.type) for a in self.args[2:]])
            return "(define-symbolic %s (~> %s %s))" % (
                self.args[0],
                args_type,
                toRosetteType(self.returnT()),
            )

        else:
            args = " ".join(
                [
                    "%s" % (a.name)
                    if isinstance(a, ValueRef) and a.name != ""
                    else "%s" % (a.toRosette(writeChoicesTo))
                    for a in self.arguments()
                ]
            )

            return "(define-bounded (%s %s) \n%s)" % (
                self.args[0],
                args,
                self.args[1].toRosette(),
            )

    def toSMT(self) -> str:
        if self.body() is None:  # uninterpreted function
            args_type = " ".join(
                parse_type_ref_to_obj(a.type).toSMTType(get_args(a.type))  # type: ignore
                for a in self.arguments()
            )
            ret_type = self.returnT()
            return "(declare-fun %s (%s) %s)" % (
                self.args[0],
                args_type,
                ret_type.toSMTType(get_args(ret_type)),  # type: ignore
            )
        else:
            declarations = []
            for a in self.arguments():
                declarations.append((a.args[0], a.type))

            args = " ".join(
                "(%s %s)" % (d[0], d[1].toSMTType(get_args(d[1]))) for d in declarations  # type: ignore
            )

            return_type = self.returnT().toSMTType(get_args(self.returnT()))  # type: ignore
            return "(define-fun-rec %s (%s) %s\n%s)" % (
                self.args[0],
                args,
                return_type,
                self.args[1] if isinstance(self.args[1], str) else self.args[1].toSMT(),
            )

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_FnDeclRecursive(self)


class FnDefine(Expr):
    def __init__(self, name: str, returnT: ObjectT, *args: Expr) -> None:
        Expr.__init__(self, FnT(returnT, *[a.type for a in args]), [name, *args])  # type: ignore

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def returnT(self) -> ObjectT:
        return self.type.args[0]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[1:]  # type: ignore

    def toRosette(
        self, writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None
    ) -> str:
        return ""  # only for verification

    def toSMT(self) -> str:
        args_type = " ".join(
            parse_type_ref_to_obj(a.type).toSMT() for a in self.args[2:]  # type: ignore
        )
        return "(declare-fun %s (%s) %s)" % (
            self.args[0],
            args_type,
            parse_type_ref_to_obj(self.type),
        )

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_FnDefine(self)


class Lambda(Expr):
    def __init__(self, returnT: Type, body: Expr, *args: Expr) -> None:
        Expr.__init__(self, FnT(returnT, *[a.type for a in args]), [body, *args])  # type: ignore

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

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Lambda(self)


class FnDecl(Expr):
    def __init__(
        self,
        name: str,
        returnT: ObjectT,
        body: Union[Expr, str],
        *args: Expr,
    ) -> None:
        self.return_type = returnT
        arg_types = tuple([arg.type for arg in args])
        fn_type = make_fn_type(returnT, *arg_types)
        Expr.__init__(self, fn_type, [name, body, *args])

    def name(self) -> str:
        return self.args[0]  # type: ignore

    def returnT(self) -> ObjectT:
        return self.return_type

    def body(self) -> Union[Expr, str]:
        return self.args[1]  # type: ignore

    def arguments(self) -> typing.List[Expr]:  # avoid name clash with Expr.args
        return self.args[2:]  # type: ignore

    def toRosette(
        self,
        writeChoicesTo: typing.Optional[Dict[str, "Expr"]] = None,
        is_uninterp: bool = False,
    ) -> str:
        if self.args[1] is None and is_uninterp:  # uninterpreted function
            args_type = " ".join(["%s" % toRosetteType(a.type) for a in self.args[2:]])
            return "(define-symbolic %s (~> %s %s))" % (
                self.args[0],
                args_type,
                toRosetteType(self.returnT()),
            )

        else:
            args = " ".join(
                [
                    "%s" % (a.name)
                    if isinstance(a, ValueRef) and a.name != ""
                    else "%s" % (a.toRosette(writeChoicesTo))
                    for a in self.arguments()
                ]
            )
            return "(define (%s %s) \n%s)" % (
                self.args[0],
                args,
                self.args[1].toRosette(),
            )

    def toSMT(self) -> str:
        if self.args[1] is None:  # uninterpreted function
            args_obj_types = [parse_type_ref_to_obj(a.type) for a in self.args[2:]]
            args_type = " ".join(
                obj_type.toSMTType(get_args(obj_type)) for obj_type in args_obj_types  # type: ignore
            )
            ret_type = parse_type_ref_to_obj(self.returnT())
            return "(declare-fun %s (%s) %s)" % (
                self.args[0],
                args_type,
                ret_type.toSMTType(get_args(ret_type)),  # type: ignore
            )
        else:
            declarations = []
            for a in self.arguments():
                declarations.append((a.args[0], a.type))

            args = " ".join(
                "(%s %s)" % (d[0], d[1].toSMTType(get_args(d[1]))) for d in declarations  # type: ignore
            )
            return_type = self.returnT().toSMTType(get_args(self.returnT()))  # type: ignore
            return "(define-fun %s (%s) %s\n%s)" % (
                self.args[0],
                args,
                return_type,
                self.args[1] if isinstance(self.args[1], str) else self.args[1].toSMT(),
            )

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_FnDecl(self)


class TargetCall(Call):
    _codegen: Optional[Callable[[Expr], str]]

    def __init__(
        self,
        name: str,
        retT: ObjectT,
        codegen: Optional[Callable[[Expr], str]],
        *args: Expr,
    ) -> None:
        super().__init__(name, retT, *args)
        self._codegen = codegen

    def codegen(self) -> str:
        return self._codegen(*self.args[1:])  # type: ignore

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_TargetCall(self)


class Target(FnDecl):
    definedFns: Dict[str, "Target"] = {}  # stores all fns that have been defined so far

    semantics: Optional[Callable[[Expr], Expr]]
    _codegen: Optional[Callable[[Expr], str]]

    def __init__(
        self,
        name: str,
        argT: typing.List[ObjectT],
        retT: ObjectT,
        semantics: Callable[[Expr], Expr],
        codegen: Callable[[Expr], str],
    ) -> None:
        args: typing.List[Expr] = [Var(f"v{i}", a) for i, a in enumerate(argT)]
        super().__init__(name, retT, semantics(*args), *args)
        self.semantics = semantics
        self._codegen = codegen
        if name in Target.definedFns:
            raise Exception(f"{name} is already defined!")
        Target.definedFns[name] = self

    def call(self, *args: Expr) -> Call:
        return TargetCall(self.name(), self.returnT(), self._codegen, *args)

    def accept(self, v: "Visitor[T]") -> T:
        return v.visit_Target(self)


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


def MLInst_Call(name: str, retType: ObjectT, *args: Union[MLInst, ValueRef]) -> MLInst:
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


class Visitor(Generic[T]):
    @abstractmethod
    def visit_Var(self, o: Var) -> T:
        pass

    @abstractmethod
    def visit_NonTerm(self, o: NonTerm) -> T:
        pass

    @abstractmethod
    def visit_Lit(self, o: Lit) -> T:
        pass

    @abstractmethod
    def visit_Object(self, o: ObjectExpr) -> T:
        pass

    @abstractmethod
    def visit_Add(self, o: Add) -> T:
        pass

    @abstractmethod
    def visit_Sub(self, o: Sub) -> T:
        pass

    @abstractmethod
    def visit_Mul(self, o: Mul) -> T:
        pass

    @abstractmethod
    def visit_Div(self, o: Div) -> T:
        pass

    @abstractmethod
    def visit_Eq(self, o: Eq) -> T:
        pass

    @abstractmethod
    def visit_Lt(self, o: Lt) -> T:
        pass

    @abstractmethod
    def visit_Le(self, o: Le) -> T:
        pass

    @abstractmethod
    def visit_Gt(self, o: Gt) -> T:
        pass

    @abstractmethod
    def visit_Ge(self, o: Ge) -> T:
        pass

    @abstractmethod
    def visit_And(self, o: And) -> T:
        pass

    @abstractmethod
    def visit_Or(self, o: Or) -> T:
        pass

    @abstractmethod
    def visit_Not(self, o: Not) -> T:
        pass

    @abstractmethod
    def visit_Implies(self, o: Implies) -> T:
        pass

    @abstractmethod
    def visit_Ite(self, o: Ite) -> T:
        pass

    @abstractmethod
    def visit_Let(self, o: Let) -> T:
        pass

    @abstractmethod
    def visit_Call(self, o: Call) -> T:
        pass

    @abstractmethod
    def visit_CallValue(self, o: CallValue) -> T:
        pass

    @abstractmethod
    def visit_Assert(self, o: Assert) -> T:
        pass

    @abstractmethod
    def visit_Constraint(self, o: Constraint) -> T:
        pass

    @abstractmethod
    def visit_TupleExpr(self, o: TupleExpr) -> T:
        pass

    @abstractmethod
    def visit_TupleGet(self, o: TupleGet) -> T:
        pass

    @abstractmethod
    def visit_Axiom(self, o: Axiom) -> T:
        pass

    @abstractmethod
    def visit_Synth(self, o: Synth) -> T:
        pass

    @abstractmethod
    def visit_Choose(self, o: Choose) -> T:
        pass

    @abstractmethod
    def visit_FnDeclRecursive(self, o: FnDeclRecursive) -> T:
        pass

    @abstractmethod
    def visit_FnDefine(self, o: FnDefine) -> T:
        pass

    @abstractmethod
    def visit_Lambda(self, o: Lambda) -> T:
        pass

    @abstractmethod
    def visit_FnDecl(self, o: FnDecl) -> T:
        pass

    @abstractmethod
    def visit_TargetCall(self, o: TargetCall) -> T:
        pass

    @abstractmethod
    def visit_Target(self, o: Target) -> T:
        pass


class ExtendedVisitor(Visitor[None]):
    def visit_Var(self, o: Var) -> None:
        pass

    def visit_NonTerm(self, o: NonTerm) -> None:
        pass

    def visit_Lit(self, o: Lit) -> None:
        pass

    def visit_Object(self, o: ObjectExpr) -> None:
        pass

    def generic_visit(self, o: Expr, args: Any = None) -> None:
        args = args if args else o.args
        for arg in args:
            arg.accept(self)

    def visit_Add(self, o: Add) -> None:
        self.generic_visit(o)

    def visit_Sub(self, o: Sub) -> None:
        self.generic_visit(o)

    def visit_Mul(self, o: Mul) -> None:
        self.generic_visit(o)

    def visit_Eq(self, o: Eq) -> None:
        self.generic_visit(o)

    def visit_Lt(self, o: Lt) -> None:
        self.generic_visit(o)

    def visit_Le(self, o: Le) -> None:
        self.generic_visit(o)

    def visit_Gt(self, o: Gt) -> None:
        self.generic_visit(o)

    def visit_Ge(self, o: Ge) -> None:
        self.generic_visit(o)

    def visit_And(self, o: And) -> None:
        self.generic_visit(o)

    def visit_Or(self, o: Or) -> None:
        self.generic_visit(o)

    def visit_Not(self, o: Not) -> None:
        self.generic_visit(o)

    def visit_Implies(self, o: Implies) -> None:
        self.generic_visit(o)

    def visit_Ite(self, o: Ite) -> None:
        self.generic_visit(o)

    def visit_Let(self, o: Let) -> None:
        self.generic_visit(o)

    def visit_Call(self, o: Call) -> None:
        self.generic_visit(o, args=o.args[1:])

    def visit_CallValue(self, o: CallValue) -> None:
        self.generic_visit(o)

    def visit_Assert(self, o: Assert) -> None:
        self.generic_visit(o)

    def visit_Constraint(self, o: Constraint) -> None:
        self.generic_visit(o)

    def visit_TupleExpr(self, o: TupleExpr) -> None:
        self.generic_visit(o)

    def visit_TupleGet(self, o: TupleGet) -> None:
        self.generic_visit(o)

    def visit_Axiom(self, o: Axiom) -> None:
        self.generic_visit(o)

    def visit_Synth(self, o: Synth) -> None:
        self.generic_visit(o, args=o.args[1:])

    def visit_Choose(self, o: Choose) -> None:
        self.generic_visit(o)

    def visit_FnDeclRecursive(self, o: FnDeclRecursive) -> None:
        self.generic_visit(o, args=o.args[1:])

    def visit_FnDefine(self, o: FnDefine) -> None:
        self.generic_visit(o, args=o.args[1:])

    def visit_Lambda(self, o: Lambda) -> None:
        self.generic_visit(o)

    def visit_FnDecl(self, o: FnDecl) -> None:
        self.generic_visit(o, args=o.args[1:])

    def visit_TargetCall(self, o: TargetCall) -> None:
        self.generic_visit(o)

    def visit_Target(self, o: Target) -> None:
        self.generic_visit(o)


class CountVarsVisitor(ExtendedVisitor):
    vars: pySet[Var]

    def __init__(self) -> None:
        self.vars = set()

    def visit_Var(self, o: Var) -> None:
        self.vars.add(o)

    def visit_NonTerm(self, o: NonTerm) -> None:
        self.vars.add(o)

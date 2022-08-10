from typing import Union, Dict, Optional, Callable

import typing

from metalift.ir import Call, Expr, IntLit, Add, Eq, BoolLit, FnDecl, getTypeName, Mul, Var


class MLObject:
    src: Expr

    def __init__(self, src: Optional[Expr]) -> None:
        self.src = src

    def typeName(self) -> str:
        if isParameterizedObject(self):
            return getTypeName(self.__orig_class__)
        else:
            return getTypeName(self.__class__)

    def toRosette(self) -> str:
        return self.src.toRosette()

    def toSMT(self) -> str:
        return self.src.toSMT()

    def codegen(self) -> str:
        return self.src.codegen()

    def __hash__(self) -> int:
        return hash(self.src)


class Bool(MLObject):
    def __init__(self, src: Union[Expr, bool] = None) -> None:
        if isinstance(src, bool):
            src = BoolLit(src)

        super().__init__(src)

    # and, or, not

    def __repr__(self):
        return f"Bool{self.src}"


class Int(MLObject):

    def __init__(self, src: Union[Expr, int]) -> None:
        if isinstance(src, int):
            src = IntLit(src)

        super().__init__(src)

    def __add__(self, other: Union[MLObject, int]) -> "Int":
        if isinstance(other, int):
            return Int(Add(self, Int(IntLit(other))))
        else:
            return Int(Add(self, other))

    def __mul__(self, other: Union[MLObject, int]) -> "Int":
        if isinstance(other, int):
            return Int(Mul(self, Int(IntLit(other))))
        else:
            return Int(Mul(self, other))

    def __eq__(self, other: Union[MLObject, int]) -> "Bool":
        if isinstance(other, int):
            return Bool(Eq(self, Int(IntLit(other))))
        else:
            return Bool(Eq(self, other))

    def __repr__(self):
        return f"Int{self.src}"

    def __hash__(self) -> int:
        return super().__hash__()

T = typing.TypeVar("T", bound=MLObject)
class List(typing.Generic[T], MLObject):

    # def __init__(self, t: Type, name: str = "") -> None:
    #     if name == "":
    #         name = f"list{List.currentNum}"
    #         List.currentNum = List.currentNum + 1
    #     Var.__init__(self, name, ListT(t))
    #     self.containedT = t

    def __init__(self, src: Expr) -> None:
        MLObject.__init__(self, src)

    @staticmethod
    def empty(t: type) -> "List":
        return List[t](Call("list_empty", List[t]))

    def length(self) -> Int:
        return Int(Call("list_length", Int, self.src))

    def __getitem__(self, index: Union[Int, int, slice]):
        containedT = self.__orig_class__.__args__[0]

        if isinstance(index, Int):
            return containedT(Call("list_get", containedT, self, index))

        elif isinstance(index, int):  # promote to Int
            return containedT(Call("list_get", containedT, self, Int(IntLit(index))))

        elif isinstance(index, slice):
            (start, stop, step) = (index.start, index.stop, index.step)

            if stop is None and step is None:
                if isinstance(start, int):
                    start = IntLit(start)
                elif isinstance(start, Int):
                    start = start.src
                return List[containedT](Call("list_tail", List[containedT], self, start))

            elif start is None and step is None:
                if isinstance(stop, int):
                    stop = IntLit(stop)
                elif isinstance(start, Int):
                    stop = stop.src
                return List[containedT](Call("list_head", List[containedT], self, stop))

            else:
                raise NotImplementedError(f"Slice not implemented: {index}")

        raise NotImplementedError(f"unknown index type: {index}")

    def __setitem__(self, index: Expr, value: Expr) -> None:
        raise NotImplementedError()

    def append(self, o: MLObject) -> "List":
        containedT = self.__orig_class__.__args__[0]
        if not isinstance(o, containedT):
            raise TypeError(f"Trying to append element of type: {type(o)} to list containing: {containedT}")
        return List[containedT](Call("list_append", List[containedT], self, o))

    # list concat
    def __add__(self, other: "List") -> "List":
        containedT = self.__orig_class__.__args__[0]
        if not isinstance(other, List):
            raise TypeError(f"can't add lists of different types: {type(other)} and {containedT}")
        return List[containedT](Call("list_concat", List[containedT], self, other))

    def __eq__(self, other: "List") -> Bool:
        containedT = self.__orig_class__.__args__[0]
        otherContainedT = other.__orig_class__.__args__[0]
        if otherContainedT != containedT:
            return Bool(BoolLit(False))
        else:
            return Bool(Call("list_eq", Bool, self, other))

    def __repr__(self):
        containedT = f"{self.__orig_class__.__args__[0].__name__}"
        return f"List[{containedT}]{self.src}"


class TargetCall(Call):
    # _codegen: Optional[Callable[[Expr], str]]

    def __init__(
        self,
        name: str,
        codegen: Optional[Callable[[MLObject], str]],
        retT: type,
        *args: MLObject,
    ) -> None:
        super().__init__(name, retT, *args)
        self._codegen = codegen


    def codegen(self) -> str:
        return self._codegen(*self.args[1:])  # type: ignore


class Target: #(FnDeclNonRecursive):
    definedFns: Dict[str, "Target"] = {}  # stores all fns that have been defined so far

    # semantics: Optional[Callable[[MLObject], MLObject]]
    # _codegen: Optional[Callable[[MLObject], str]]

    def __init__(
        self,
        name: str,
        argT: typing.List[type],
        retT: type,
        semantics: Callable[[MLObject], Expr],
        codegen: Callable[[MLObject], str],
    ) -> None:

        # args: typing.List[Var] = []
        # for i, a in enumerate(argT):
        #     if isList(a):
        #         # args.append(List(typing.cast(ListT, a).args[0]))
        #         args.append(List(Int)) # , typing.cast(ListT, a).args[0]))
        #     else:
        #         args.append(Var(f"v{i}", a))
        #
        # # super().__init__(name, retT, semantics(*args), *args)
        # super().__init__(name, retT, None, Var("list1", ListT(Int()))) #"*args)
        self.name = name
        self.argT = argT
        self.retT = retT
        self.semantics = semantics
        self._codegen = codegen


        if name in Target.definedFns:
            raise Exception(f"{name} is already defined!")
        Target.definedFns[name] = self

    def call(self, *args: MLObject) -> MLObject:
        # return self.retT(Call(self.name, self.retT, *args))
        return self.retT(TargetCall(self.name, self._codegen, self.retT, *args))

    def decl(self) -> FnDecl:
        args = [ a(Var(f"arg{i}", a)) for (i, a) in enumerate(self.argT) ]
        return FnDecl(self.name, self.retT, self.semantics(*args), *args)

    def body(self) -> Expr:
        args = [ a(Var(f"arg{i}", a)) for (i, a) in enumerate(self.argT) ]
        return self.semantics(*args)


        # if not self.args[1]:
        #     args: typing.List[Var] = []
        #     for i, a in enumerate(self.argT):
        #         if isList(a):
        #             args.append(List(typing.cast(ListT, a).args[0]))
        #         else:
        #             args.append(Var(f"v{i}", a))
        #     self.args[1] = self.semantics(*args)
        #     self.args[2] = args
        # return self.args[1]


def isParameterizedType(t: type) -> bool:
    return "__origin__" in t.__dict__

def isParameterizedObject(o: MLObject) -> bool:
    return "__orig_class__" in o.__dict__

def getType(o: MLObject) -> type:
    return o.__orig_class__ if isParameterizedObject(o) else type(o)

from abc import abstractclassmethod
from typing import Union, Dict, Optional, Callable

import typing
from metalift.frontend.python import Driver

from metalift.ir import And, Call, Expr, Gt, Ge, IntLit, Add, Eq, BoolLit, FnDecl, Lt, Le, Mul, Not, Or, Sub, Var
from metalift.types import ListT, Type, getTypeName, Int as IntT, Bool as BoolT


class MLObject:
    src: Expr
    driver: Driver

    def __init__(self, driver: Driver, src: Expr) -> None:
        self.driver = driver
        self.src = src

    def type_name(self) -> str:
        if isParameterizedObject(self):
            return getTypeName(self.__orig_class__)
        else:
            return getTypeName(self.__class__)

    def to_rosette(self) -> str:
        return self.src.toRosette()

    def to_SMT(self) -> str:
        return self.src.toSMT()

    def codegen(self) -> str:
        return self.src.codegen()

    def __hash__(self) -> int:
        return hash(self.src)

    @abstractclassmethod
    def expr_type() -> Type:
        raise NotImplementedError()


class Bool(MLObject):

    def __init__(self, driver: Driver, value: Optional[Union[bool, str, Expr]] = None) -> None:
        if value is None:  # a symbolic variable
            src = driver.variable("v", BoolT())  # XXX: change to Bool 
        elif isinstance(value, bool):
            src = BoolLit(value)
        elif isinstance(value, Expr):
            if value.type != BoolT():
                raise TypeError(f"Cannot create Bool from {value.type}")
            src = value            
        else:
            raise TypeError(f"Cannot create Bool from {value}")
       
        super().__init__(driver, src)


    # python doesn't have hooks for and, or, not
    @staticmethod
    def And(e: "Bool", *es: "Bool") -> "Bool":
        return Bool(e.driver, And(e.src, *es))
    
    @staticmethod
    def Or(e: "Bool", *es: "Bool") -> "Bool":
        return Bool(e.driver, Or(e.src, *es))
    
    @staticmethod
    def Not(e: "Bool") -> "Bool":
        return Bool(e.driver, Not(e.src))

    def __eq__(self, other: Union["Bool", bool]) -> "Bool":
        if isinstance(other, bool):
            other = Bool(self.driver, BoolLit(other))
        return Bool(self.driver, Eq(self.src, other.src))
        
    def __ne__(self, other: Union["Bool", bool]) -> "Bool":
        if isinstance(other, bool):
            other = Bool(self.driver, BoolLit(other))
        return Bool(self.driver, Not(Eq(self.src, other.src)))
    
    


    @staticmethod
    def expr_type() -> Type:
        return BoolT()

    def __repr__(self):
        return f"Bool{self.src}"


class Int(MLObject):

    def __init__(self, driver: Driver, value: Optional[Union[int, Expr]] = None) -> None:
        if value is None:  # a symbolic variable
            src = driver.variable("v", IntT())  # change to Int
        elif isinstance(value, int):
            src = IntLit(value)
        elif isinstance(value, Expr):
            if value.type != IntT():
                raise TypeError(f"Cannot create Int from {value.type}")
            src = value
        else:
            raise TypeError(f"Cannot create Int from {value}")
       
        super().__init__(driver, src)

    @staticmethod
    def expr_type() -> Type:
        return IntT()

    def binary_op(self, other: Union["Int", int], op: Callable[[Expr, Expr], Expr]) -> "Int":
        if isinstance(other, Int):
            return Int(self.driver, op(self.src, other.src))
        elif isinstance(other, int):
            return Int(self.driver, op(self.src, IntLit(other)))
        else:
            raise TypeError(f"Cannot call {op} on Int and {other}")


    # arithmetic operators
    def __add__(self, other: Union["Int", int]) -> "Int":
        return self.binary_op(other, Add)

    def __sub__(self, other: Union["Int", int]) -> "Int":
        return self.binary_op(other, Sub)

    def __mul__(self, other: Union["Int", int]) -> "Int":
        return self.binary_op(other, Mul)

    # div not supported yet

    def __radd__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(IntLit(other)) + self
        else:
            return other + self
    
    def __rsub__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(IntLit(other)) - self
        else:
            return other - self
    
    def __rmul__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(IntLit(other)) * self
        else:
            return other * self

    # logical comparison operators
    def __eq__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, IntLit(other))
        return Bool(self.driver, Eq(self.src, other.src))
        
    def __ne__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, IntLit(other))
        return Bool(self.driver, Not(Eq(self.src, other.src)))

    def __ge__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, IntLit(other))
        return Bool(self.driver, Ge(self.src, other.src))

    def __gt__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, IntLit(other))
        return Bool(self.driver, Gt(self.src, other.src))

    def __lt__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, IntLit(other))
        return Bool(self.driver, Lt(self.src, other.src))

    def __le__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, IntLit(other))
        return Bool(self.driver, Le(self.src, other.src))


    def __repr__(self):
        return f"Int{self.src}"

    def __hash__(self) -> int:
        return super().__hash__()


T = typing.TypeVar("T", bound=MLObject)
class List(typing.Generic[T], MLObject):
    containedT: Type
    driver: Driver

    def __init__(self, driver: Driver, containedT: Type, value: Optional[Union[Expr, str]] = None) -> None:
        
        # containedT is either a type or a typing._GenericAlias
        # typing._GenericAlias has __origin__ and __args__ attributes
                    
        self.containedT = containedT
        self.driver = driver

        if value is None:  # a symbolic variable
            src = driver.variable("v", ListT(containedT))
        elif isinstance(value, Expr):
            if value.type.name != "MLList":
                raise TypeError(f"Cannot create List from {value.type}")
            src = value
        elif isinstance(value, str):
            # XXX add support for nested list. containedT will be a _GenericAlias
            src = driver.variable(value, ListT(containedT))
        else:
            raise TypeError(f"Cannot create List from {value}")
       
        super().__init__(driver, src)


    @staticmethod
    def empty(driver: Driver, t: Type) -> "List":
        return List(driver, t, Call("list_empty", ListT(t.expr_type())))

    # @staticmethod
    # def expr_type() -> Type:
    #     return ListT()

    def __len__(self) -> Int:
        return Int(self.driver, Call("list_length", IntT(), self.src))

    def __getitem__(self, index: Union[Int, int]) -> Expr:  # index can also be slice
        # containedT = self.__orig_class__.__args__[0]

        if isinstance(index, int):  # promote to Int
            index = Int(self.driver, index)

        return self.containedT(self.driver, Call("list_get", self.src.type.args[0], self.src, index.src))

        # elif isinstance(index, slice):
        #     (start, stop, step) = (index.start, index.stop, index.step)

        #     if stop is None and step is None:
        #         if isinstance(start, int):
        #             start = IntLit(start)
        #         elif isinstance(start, Int):
        #             start = start.src
        #         return List[containedT](Call("list_tail", List[containedT], self, start))

        #     elif start is None and step is None:
        #         if isinstance(stop, int):
        #             stop = IntLit(stop)
        #         elif isinstance(start, Int):
        #             stop = stop.src
        #         return List[containedT](Call("list_head", List[containedT], self, stop))

        #     else:
        #         raise NotImplementedError(f"Slice not implemented: {index}")
        

    def __setitem__(self, index: Union[Int, int], value: MLObject) -> None:
        if isinstance(index, int):  # promote to Int
            index = IntLit(index)

        # containedT = self.__orig_class__.__args__[0]
        if value.type != self.containedT:
            raise TypeError(f"Trying to set list element of type: {value.type} to list containing: {self.containedT}")
        
        return List(self.driver, self.containedT, Call("list_set", self.src.type, self.src, index.src, value.src))
        

    def append(self, o: MLObject) -> "List":
        # containedT = self.__orig_class__.__args__[0]
        if type(o) != self.containedT:
            raise TypeError(f"Trying to append element of type: {o.type} to list containing: {self.containedT}")
        
        return List(self.driver, self.containedT, Call("list_append", self.src.type, self.src, o.src))

    # # list concat
    def __add__(self, other: "List") -> "List":
        # containedT = self.__orig_class__.__args__[0]
        if type(other) != type(self):
            raise TypeError(f"can't add lists of different types: {type(other)} and {type(self)}")
        return List(self.driver, self.containedT, Call("list_concat", self.src.type, self, other))


    def __eq__(self, other: "List") -> Bool:        
        if type(other) != type(self):
            return Bool(BoolLit(False))
        else:
            return Bool(self.driver, Call("list_eq", BoolT(), self.src, other.src))


    def __repr__(self):
        # containedT = f"{self.__orig_class__.__args__[0].__name__}"
        # return f"List[{containedT}]({self.src})"
        return f"List[{self.containedT}]({self.src})"





def isParameterizedType(t: type) -> bool:
    return "__origin__" in t.__dict__

def isParameterizedObject(o: MLObject) -> bool:
    return "__orig_class__" in o.__dict__

def getType(o: MLObject) -> type:
    return o.__orig_class__ if isParameterizedObject(o) else type(o)



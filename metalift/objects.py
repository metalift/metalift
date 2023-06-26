# from abc import abstractclassmethod
from typing import Generic, TypeVar, Union, Optional, Callable

from typing import _GenericAlias
import typing
from metalift.frontend.python import Driver
from metalift.frontend.utils import qual_name

from metalift.ir import And, Call, Expr, Gt, Ge, IntLit, Add, Eq, BoolLit, Lt, Le, Mul, Not, Or, Sub
from metalift.types import Type, getTypeName


class Object(Expr):
    driver: Driver
    src: Expr

    def __init__(self, driver: Driver, src: Expr, type: Union[type, _GenericAlias]) -> None:
        self.driver = driver
        self.src = src  # pass this to parent class?
        super().__init__(type, None)

    def type_name(self) -> str:
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

    # @abstractclassmethod
    # def Expr_type() -> Type:
    #     raise NotImplementedError()


class Bool(Object):

    def __init__(self, driver: Driver, value: Optional[Union[bool, str, Expr]] = None) -> None:
        if value is None:  # a symbolic variable
            src = driver.variable("v", Bool) # XXX change to Bool
        elif isinstance(value, bool):
            src = BoolLit(value)
        elif isinstance(value, Expr):
            # if value.type != BoolT() and 
            # if value.type != Bool: # XXX change to Bool
            #     raise TypeError(f"Cannot create Bool from {value.type}")
            src = value            
        else:
            raise TypeError(f"Cannot create Bool from {value}")
       
        super().__init__(driver, src, Bool)


    # python doesn't have hooks for and, or, not
    def And(self, *args: "Bool") -> "Bool":      
        if len(args) == 0:
            raise Exception(f"Arg list must be non-empty: {args}")
        # if not all(map(lambda e: e.type == Bool, args)):
        #     raise Exception(f"Cannot apply AND to values of type {args}")
        return Bool(self.driver, And(self, *args))
    
    def Or(self, *args: "Bool") -> "Bool":
        if len(args) < 1:
            raise Exception(f"Arg list must be non-empty: {args}")
        # if not all(map(lambda e: e.type == Bool, args)):
        #     raise Exception(
        #         f"Cannot apply OR to values of type {map(lambda e: e.type, args)}"
        #     )
        return Bool(self.driver, Or(self, *args))
    
    def Not(self) -> "Bool":
        return Bool(self.driver, Not(self))

    def __eq__(self, other: Union["Bool", bool]) -> "Bool":
        if isinstance(other, bool):
            other = Bool(self.driver, other)
        return Bool(self.driver, Eq(self, other))
        
    def __ne__(self, other: Union["Bool", bool]) -> "Bool":
        if isinstance(other, bool):
            other = Bool(self.driver, other)
        return Bool(self.driver, Not(Eq(self, other)))
    
    
    # @staticmethod
    # def Expr_type() -> Type:
    #     return BoolT()

    def __repr__(self):
        return f"Bool({self.src})"


class Int(Object):

    def __init__(self, driver: Driver, value: Optional[Union[int, str, Expr]] = None) -> None:
        if value is None:  # a symbolic variable
            src = driver.variable("v", Int)  # XXX change to Int
        elif isinstance(value, int):
            src = IntLit(value)            
        elif isinstance(value, Expr):     
            # if value.type != IntT() and 
            # if value.type != Int: # XXX change to Int
            #     raise TypeError(f"Cannot create Int from {value.type}")       
            src = value
        elif isinstance(value, str):
            src = driver.variable(value, Int)
        else:
            raise TypeError(f"Cannot create Int from {value}")
       
        super().__init__(driver, src, Int)

    # @staticmethod
    # def Expr_type() -> Type:
    #     return IntT()

    def toRosette(self) -> str:
        return self.src.toRosette()

    def binary_op(self, other: Union["Int", int], op: Callable[[Expr, Expr], Expr]) -> "Int":
        if isinstance(other, Int) or isinstance(other, int):
            return Int(self.driver, op(self, other))
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
            return Int(self.driver, other) + self
        else:
            return other + self
    
    def __rsub__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(self.driver, other) - self
        else:
            return other - self
    
    def __rmul__(self, other: Union["Int", int]) -> "Int":
        if isinstance(other, int):
            return Int(self.driver, other) * self
        else:
            return other * self

    # logical comparison operators
    def __eq__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, other)
        return Bool(self.driver, Eq(self, other))
        
    def __ne__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, other)
        return Bool(self.driver, Not(Eq(self, other)))

    def __ge__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, other)
        return Bool(self.driver, Ge(self, other))

    def __gt__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, other)
        return Bool(self.driver, Gt(self, other))

    def __lt__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, other)
        return Bool(self.driver, Lt(self, other))

    def __le__(self, other: Union["Int", int]) -> Bool:
        if isinstance(other, int):
            other = Int(self.driver, other)
        return Bool(self.driver, Le(self, other))


    def __repr__(self):
        return f"Int({self.src})"

    def __hash__(self) -> int:
        return super().__hash__()


T = TypeVar("T", bound=Object)
class List(Generic[T], Object):

    def __init__(self, driver: Driver, containedT: Union[type, _GenericAlias], value: Optional[Union[Expr, str]] = None) -> None:
        # typing._GenericAlias has __origin__ and __args__ attributes, use get_origin and get_args to access
                    
        if value is None:  # a symbolic variable
            src = driver.variable("v", List[containedT])
        elif isinstance(value, Expr):
            src = value
        elif isinstance(value, str):
            src = driver.variable(value, List[containedT])
        else:
            raise TypeError(f"Cannot create List from {value}")
       
        super().__init__(driver, src, List[containedT])


    @staticmethod
    def empty(driver: Driver, containedT: Union[type, _GenericAlias]) -> "List":
        return List(driver, containedT, Call("list_empty", List[containedT]))

    # @staticmethod
    # def Expr_type() -> Type:
    #     return ListT()

    def __len__(self) -> int:
        raise NotImplementedError("len must return an int, call len() instead")
    
    def len(self) -> Int:
        return Int(self.driver, Call("list_length", Int, self.src))

    def __getitem__(self, index: Union[Int, int]) -> Expr:  # index can also be slice
        if isinstance(index, int):  # promote to Int
            index = Int(self.driver, index)

        containedT = typing.get_args(self.type)[0]  
        if isinstance(containedT, type): # non generic type
            return containedT(self.driver, Call("list_get", containedT, self.src, index.src))
        elif isinstance(containedT, _GenericAlias): # generic type 
            subcontainedT = typing.get_args(containedT)[0]
            return containedT(self.driver, subcontainedT, Call("list_get", containedT, self.src, index.src))
        else:
            raise NotImplementedError(f"Cannot get item from list containing type {containedT}")


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
        

    def __setitem__(self, index: Union[Int, int], value: T) -> None:
        if isinstance(index, int):  # promote to Int
            index = Int(self.driver, index)

        containedT = typing.get_args(self.type)[0]
        if value.type != containedT:
            raise TypeError(f"Trying to set list element of type: {value.type} to list containing: {containedT}")
        
        self.src = Call("list_set", self.type, self.src, index.src, value.src)
        
    # in place append
    def append(self, value: T) -> None:
        containedT = typing.get_args(self.type)[0]
        if value.type != containedT:
            raise TypeError(f"Trying to append element of type: {value.type} to list containing: {containedT}")

        self.src = Call("list_append", self.type, self.src, value.src)

    # list concat that returns a new list
    def __add__(self, other: "List") -> "List":
        if other.type != self.type:
            raise TypeError(f"can't add lists of different types: {other.type} and {self.type}")
        containedT = typing.get_args(self.type)[0]
        return List(self.driver, containedT, Call("list_concat", self.type, self.src, other.src))


    def __eq__(self, other: "List") -> Bool:        
        if other.type != self.type:
            return Bool(self.driver, False)
        else:
            return Bool(self.driver, Call("list_eq", Bool, self.src, other.src))


    def __repr__(self):
        return f"{qual_name(self.type)}({self.src})"





def isParameterizedType(t: type) -> bool:
    return "__origin__" in t.__dict__

def isParameterizedObject(o: Object) -> bool:
    return "__orig_class__" in o.__dict__

def getType(o: Object) -> type:
    return o.__orig_class__ if isParameterizedObject(o) else type(o)



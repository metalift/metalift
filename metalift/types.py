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
            or self.name == "EnumInt"
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

    # def erase(self) -> "Type":
    #     if (
    #         self.name == "ClockInt"
    #         or self.name == "EnumInt"
    #         or self.name == "OpaqueInt"
    #         or self.name == "NodeIDInt"
    #     ):
    #         return Int()
    #     else:
    #         return Type(
    #             self.name, *[a.erase() if isinstance(a, Type) else a for a in self.args]
    #         )

    # def __eq__(self, other: object) -> bool:
    #     if isinstance(other, Type):
    #         if self.name != other.name or len(self.args) != len(other.args):
    #             return False
    #         else:
    #             return all(
    #                 a1 == a2
    #                 if isinstance(a1, type) and isinstance(a2, type)
    #                 else a1.__eq__(a2)
    #                 for a1, a2 in zip(self.args, other.args)
    #             )
    #     return NotImplemented

    # def __ne__(self, other: object) -> bool:
    #     x = self.__eq__(other)
    #     if x is not NotImplemented:
    #         return not x
    #     return NotImplemented

    # def __hash__(self) -> int:
    #     return hash(tuple(sorted({"name": self.name, "args": tuple(self.args)})))


# def Int() -> Type:
#     return Type("Int")


# def ClockInt() -> Type:
#     return Type("ClockInt")


# def EnumInt() -> Type:
#     return Type("EnumInt")


# def OpaqueInt() -> Type:
#     return Type("OpaqueInt")


# def NodeIDInt() -> Type:
#     return Type("NodeIDInt")


# def Bool() -> Type:
#     return Type("Bool")


# for string literals
def String() -> Type:
    return Type("String")


def PointerT(t: Type) -> Type:
    return Type("Pointer", t)


# def ListT(contentT: Type) -> Type:
#     return Type("MLList", contentT)


def FnT(retT: Type, *argT: Type) -> Type:
    return Type("Function", retT, *argT)


# def SetT(contentT: Type) -> Type:
#     return Type("Set", contentT)


def MapT(keyT: Type, valT: Type) -> Type:
    return Type("Map", keyT, valT)


# # first type is not optional
# def TupleT(e1T: Type, *elemT: Type) -> Type:
#     return Type("Tuple", e1T, *elemT)


# def getTypeName(t: type) -> str:
#     if isinstance(
#         t, typing._GenericAlias
#     ):  # parameterized class -- python 3.9 has types.GenericAlias
#         args = ",".join(a.__name__ for a in t.__args__)
#         return f"{t.__origin__.__name__}[{args}]"
#     else:
#         return f"{t.__name__}"

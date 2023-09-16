import typing

# print the short name of a type: a.b.c.D -> D
def qual_name(t: type) -> str:
    if isinstance(t, type):
        return t.__qualname__
    elif isinstance(t, typing._GenericAlias):
        args = typing.get_args(t)
        return f"{qual_name(typing.get_origin(t))}[{' '.join(qual_name(arg) for arg in args)}]"
    else:
        raise NotImplementedError(t)

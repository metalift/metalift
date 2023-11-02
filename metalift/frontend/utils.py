import typing

from metalift.ir import Expr

# print the short name of a type: a.b.c.D -> D
def qual_name(t: type) -> str:
    if isinstance(t, type):
        return t.__qualname__
    elif isinstance(t, typing._GenericAlias):
        args = typing.get_args(t)
        return f"{qual_name(typing.get_origin(t))}[{' '.join(qual_name(arg) for arg in args)}]"
    else:
        raise NotImplementedError(t)


class ExprDict:
    def __init__(self) -> None:
        self.kv_pairs = []

    def __getitem__(self, key: Expr) -> typing.Any:
        for k, v in self.kv_pairs:
            if Expr.__eq__(k, key):
                return v
        raise Exception(f"{key} does not exist!")

    def __setitem__(self, key: Expr, value: typing.Any) -> None:
        for i, (k, _) in enumerate(self.kv_pairs):
            if Expr.__eq__(k, key):
                self.kv_pairs[i] = (k, value)
                return
        self.kv_pairs.append((key, value))

    def __contains__(self, key: Expr):
        return any([Expr.__eq__(k, key) for (k, _) in self.kv_pairs])

    def __len__(self):
        return len(self.kv_pairs)

    def keys(self) -> typing.List[Expr]:
        return [kv_pair[0] for kv_pair in self.kv_pairs]

    def values(self) -> typing.List[typing.Any]:
        return [kv_pair[1] for kv_pair in self.kv_pairs]

    def items(self) -> typing.List[Expr]:
        return self.kv_pairs


class ExprSet:
    def __init__(self, exprs: typing.List[Expr]) -> None:
        self.exprs: typing.List[Expr] = []
        for expr in exprs:
            if not any([Expr.__eq__(expr, e) for e in self.exprs]):
                self.exprs.append(expr)

    def __contains__(self, key: Expr) -> bool:
        return any([Expr.__eq__(expr, key) for expr in self.exprs])

    def __sub__(self, other_set: "ExprSet") -> "ExprSet":
        new_exprs: typing.List[Expr] = []
        for expr in self.exprs:
            if not expr in other_set:
                new_exprs.append(expr)
        return ExprSet(new_exprs)

    def __iter__(self):
        for expr in self.exprs:
            yield expr

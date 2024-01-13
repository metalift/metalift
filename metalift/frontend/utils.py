import typing
from typing import Any, Generator, Iterable, List

from metalift.ir import Expr, Object


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
        self.kv_pairs = []  # type: ignore

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

    def __contains__(self, key: Expr) -> bool:
        return any([Expr.__eq__(k, key) for (k, _) in self.kv_pairs])

    def __len__(self) -> int:
        return len(self.kv_pairs)

    def keys(self) -> typing.List[Expr]:
        return [kv_pair[0] for kv_pair in self.kv_pairs]

    def values(self) -> typing.List[typing.Any]:
        return [kv_pair[1] for kv_pair in self.kv_pairs]

    def items(self) -> typing.List[Expr]:
        return self.kv_pairs


class ObjectSet:
    def __init__(self, objs: Iterable[Object] = []) -> None:
        self.objs: typing.List[Object] = []
        for obj in objs:
            if not any([Object.__eq__(obj, o) for o in self.objs]):
                self.objs.append(obj)

    def add(self, key: Object) -> None:
        existed = False
        for obj in self.objs:
            if Object.__eq__(obj, key):
                existed = True
        if not existed:
            self.objs.append(key)

    def __contains__(self, key: Object) -> bool:
        return any([Object.__eq__(obj, key) for obj in self.objs])

    def __sub__(self, other_set: "ObjectSet") -> "ObjectSet":
        new_objs: typing.List[Object] = []
        for obj in self.objs:
            if not obj in other_set:
                new_objs.append(obj)
        return ObjectSet(new_objs)

    def __add__(self, other_set: "ObjectSet") -> "ObjectSet":
        new_objs = ObjectSet()
        for obj in self.objs:
            if not obj in new_objs:
                new_objs.add(obj)
        for obj in other_set.objs:
            if not obj in new_objs:
                new_objs.add(obj)
        return new_objs

    def __iter__(self) -> Generator[Object, Any, None]:
        for new_objs in self.objs:
            yield new_objs

    def objects(self) -> List[Object]:
        return self.objs

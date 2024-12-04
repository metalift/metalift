import re
from typing import (
    Any,
    Callable,
    Dict,
    Iterable,
    List,
    NamedTuple,
    Optional,
    Set,
    Tuple,
    Union,
    cast,
)

from llvmlite import binding as llvm
from llvmlite.binding import ValueRef

from metalift.ir import (
    Bool,
    Expr,
    Lit,
    MLInst,
    MLInst_Assert,
    MLInst_Assume,
    MLInst_Call,
    MLInst_Eq,
    MLInst_Havoc,
    MLInst_Load,
    MLInst_Not,
    MLInst_Or,
    MLInst_Return,
    ObjectT,
    Synth,
    Var,
)
from metalift.vc import VC, Block

orig_value_ref_operands = ValueRef.operands


@property  # type: ignore
def new_value_ref_operands(self: ValueRef) -> Any:
    if hasattr(self, "my_operands") and self.my_operands:
        return self.my_operands
    else:
        return orig_value_ref_operands.__get__(self)


setattr(ValueRef, "operands", new_value_ref_operands)


def setupBlocks(blks: Iterable[ValueRef]) -> Dict[str, Block]:
    bbs = dict((b.name, Block(b.name, list(b.instructions))) for b in blks)

    for b in bbs.values():
        i = b.instructions[-1]
        opcode = i.opcode
        ops = list(i.operands)

        if opcode == "br":
            targets = ops[0:] if len(ops) == 1 else ops[1:]
        elif opcode == "switch":
            targets = ops[1::2]
        elif opcode == "ret":
            targets = []
        else:
            raise Exception("Unknown end block inst: %s" % i)

        b.succs = [bbs[t.name] for t in targets]

        for t in targets:
            bbs[t.name].preds.append(b)

    return bbs


# replace ret void with ret sret argument if srets are used
def parseSrets(fnArgs: List[ValueRef], blks: Iterable[Block]) -> None:
    sret = None
    for a in fnArgs:
        if b"sret" in a.attributes:
            if sret is None:
                sret = a
            else:
                raise Exception("multiple sret arguments: %s and %s" % (sret, a))

    if sret:
        for b in blks:
            if b.instructions[-1].opcode == "ret":
                ops = list(b.instructions[-1].operands)
                if len(ops):
                    raise Exception("return val not void: %s" % b.instructions[-1])
                else:
                    b.instructions[-1] = MLInst_Return(sret)


# previous attempt in rewriting all STL vector fn calls
# def lowerVectorCalls(blks):
#   for b in blks:
#     for i in range(len(b.instructions)):
#       inst = b.instructions[i]
#
#       if inst.opcode == "call":
#         ops = list(inst.operands)
#         fnName = ops[-1].name
#         if fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEEC1Ev":
#           newInst = MLInstruction("call", "newlist")
#           newInst.name = ops[0].name
#           newInst.type = ops[0].type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNKSt3__16vectorIiNS_9allocatorIiEEE4sizeEv":
#           newInst = MLInstruction("call", ops[0], "listLength")
#           newInst.name = inst.name
#           newInst.type = inst.type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEEixEm":
#           newInst = MLInstruction("call", ops[0], ops[1], "listGet")
#           newInst.name = inst.name
#           newInst.type = inst.type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEE9push_backERKi":
#           newInst = MLInstruction("call", ops[0], ops[1], "listAppend")
#           newInst.name = ops[0].name
#           newInst.type = ops[0].type
#           b.instructions[i] = newInst
#
#         elif fnName == "_ZNSt3__16vectorIiNS_9allocatorIiEEED1Ev": # destructor
#           newInst = MLInstruction("call", ops[0], "listDestruct")
#           b.instructions[i] = newInst

LoopInfo = NamedTuple(
    "LoopInfo",
    [
        ("header", List[str]),
        ("body", List[str]),
        ("exits", List[str]),
        ("latches", List[str]),
    ],
)


def parseLoops(filename: str, fnName: str, log: bool = True) -> List[LoopInfo]:
    with open(filename, mode="r") as f:
        foundLines = []
        found = False
        for l in f.readlines():
            if re.match(
                "Printing analysis 'Natural Loop Information' for function '%s':"
                % fnName,
                l,
            ):
                found = True
            elif found:
                loopMatch = re.match("Loop at depth \d+ containing: (\S+)", l.strip())
                if loopMatch:
                    foundLines.append(loopMatch.group(1))
                elif re.match(
                    "Printing analysis 'Natural Loop Information' for function '\S+':",
                    l,
                ):
                    found = False

        loops: List[LoopInfo] = []
        for m in foundLines:
            header = []
            body = []
            exits = []
            latches = []

            blks = m.replace("%", "").split(",")
            for b in blks:
                name: str = re.search("([^<]+)", b).group(0)  # type: ignore
                if log:
                    print("name: %s" % b)
                if "<header>" in b:
                    header.append(name)
                if "<exiting>" in b:
                    exits.append(name)
                if "<latch>" in b:
                    latches.append(name)
                if "<header>" not in b and "<exiting>" not in b and "latch" not in b:
                    body.append(name)

            loops.append(LoopInfo(header, body, exits, latches))

        if log:
            for loop in loops:
                print(
                    "found loop: header: %s, body: %s, exits: %s, latches: %s"
                    % (loop.header, loop.body, loop.exits, loop.latches)
                )

        return loops


class CodeInfo:
    def __init__(
        self,
        name: str,
        retT: ObjectT,
        modifiedVars: List[Union[ValueRef, Expr]],
        readVars: List[Union[ValueRef, Expr]],
    ) -> None:
        self.name = name
        self.retT = retT
        self.modified_vars = modifiedVars
        self.read_vars = readVars

    def __repr__(self) -> str:
        return "name: %s\nret type: %s\nmod vars: %s\nread args: %s" % (
            self.name,
            self.retT,
            [
                v.name if isinstance(v, ValueRef) else v.args[0]
                for v in self.modified_vars
            ],
            [v.name if isinstance(v, ValueRef) else v.args[0] for v in self.read_vars],
        )


invNum = 0


def processLoops(
    header: Block,
    body: List[Block],
    exits: List[Block],
    latches: List[Block],
    fnArgs: List[ValueRef],
) -> CodeInfo:
    havocs = []
    for blk in [header, *body, *exits, *latches]:
        for i in blk.instructions:
            opcode = i.opcode
            ops = list(i.operands)
            # prevent duplicate havocs in nested loops
            # TODO : why are havocs only from store instructions
            if opcode == "store" and ops[1] not in havocs:
                havocs.append(ops[1])

    global invNum
    inv = MLInst_Call(
        "inv%s" % invNum, Bool, *[MLInst_Load(h) for h in havocs], *fnArgs
    )
    invNum = invNum + 1

    # remove back edges, and replace br with assert inv
    for l in latches:
        l.succs.remove(header)
        header.preds.remove(l)
        l.instructions[-1] = MLInst_Assert(inv)

    # prepend assume inv to header
    header.instructions.insert(0, MLInst_Assume(inv))

    # prepend havocs to header
    if havocs:
        header.instructions.insert(0, MLInst_Havoc(*havocs))

    # append assert inv initialization to header's predecessor
    for p in header.preds:
        p.instructions.insert(-1, MLInst_Assert(inv))

    print("header preds:")
    for p in header.preds:
        for i in p.instructions:
            print("%s" % i)

    print("header:")
    for i in header.instructions:
        print("%s" % i)

    # print("exits:")
    # for e in exits:
    #   for i in e.instructions:
    #     print("%s" % i)

    print("latches:")
    for l in latches:
        print("%s: succ: %s" % (l.name, l.succs))
        for i in l.instructions:
            print("%s" % i)

    return CodeInfo(inv.operands[0], Bool(), havocs, fnArgs)  # type: ignore


def processBranches(
    blocksMap: Dict[str, Block],
    fnArgs: List[ValueRef],
    wrapSummaryCheck: Optional[Callable[[MLInst], Tuple[Expr, List[Expr]]]] = None,
    fnName: str = "ps",
) -> List[CodeInfo]:
    retCodeInfo = []
    for b in blocksMap.values():
        opcode = b.instructions[-1].opcode
        ops = list(b.instructions[-1].operands)

        if opcode == "br" and len(ops) > 1:  # a conditional branch
            # XXX: bug in llvmlite that switches the ordering of succs
            b.succs[1].instructions.insert(0, MLInst_Assume(ops[0]))
            b.succs[0].instructions.insert(0, MLInst_Assume(MLInst_Not(ops[0])))

        elif opcode == "switch":
            targets = ops[3::2]
            vals = ops[2::2]
            for t, v in zip(targets, vals):
                blocksMap[t.name].instructions.insert(
                    0, MLInst_Assume(MLInst(ops[0], v))
                )

            # default fallthrough
            blocksMap[ops[1].name].instructions.insert(
                0,
                MLInst_Assume(
                    MLInst_Not(MLInst_Or(*[MLInst_Eq(ops[0], v) for v in vals]))
                ),
            )

        elif opcode == "ret":
            returnArg = ops[0]
            filteredArgs = list(
                filter(lambda a: b"sret" not in a.attributes, fnArgs)
            )  # remove the sret args
            ps: Union[MLInst, Expr] = MLInst_Call(
                fnName, Bool, returnArg, *filteredArgs
            )
            # TODO: not sure what wrapSummaryCheck is doing
            if wrapSummaryCheck:
                ps, transformedArgs = wrapSummaryCheck(cast(MLInst, ps))
                returnArg = transformedArgs[0]
                filteredArgs = transformedArgs[1:]
            b.instructions.insert(-1, MLInst_Assert(ps))
            retCodeInfo.append(CodeInfo(fnName, Bool, [returnArg], filteredArgs))

    return retCodeInfo


def parseGlobals(
    global_variables: List[ValueRef], log: bool = True
) -> Dict[str, ValueRef]:
    globalVars = {}
    for g in global_variables:
        if re.search("\[. x i8\]\*", str(g.type)):  # strings have type [n x i8]*
            o = re.search('"(.+)"', str(g))
            if o:
                v = o.group(1).replace("\\00", "")
            else:
                raise Exception("failed to match on type: %s" % str(g.type))
            globalVars[g.name] = v

    if log:
        print("globals:")
        for k, v in globalVars.items():
            print("%s -> %s" % (k, v))
    return globalVars


def parseObjectFuncs(blocksMap: Dict[str, Block]) -> None:
    p = re.compile("ML_(\w+)_(set|get)_(\w+)")
    for b in blocksMap.values():
        for i in b.instructions:
            opcode = i.opcode
            ops = list(i.operands)

            if opcode == "call":
                fnName = ops[-1].name
                r = p.search(fnName)
                if r:
                    className = r.group(1)  # not used
                    op = r.group(2)
                    fieldName = r.group(3)
                    if op == "set":
                        # newInst = MLInst_Call("setField", i.type, Lit(fieldName, String()), ops[0], ops[1])
                        setattr(
                            i,
                            "my_operands",
                            [
                                Lit(fieldName, String()),  # type: ignore
                                ops[0],
                                ops[1],
                                "setField",
                            ],
                        )
                    else:
                        # i.operands = ["getField", i.type, Lit(fieldName, String()), ops[0], "getField"]
                        setattr(
                            i,
                            "my_operands",
                            [Lit(fieldName, String()), ops[0], "getField"],  # type: ignore
                        )
                        # print("inst: %s" % i)


# run all code analysis
def analyze(
    filename: str,
    fnName: str,
    loopsFile: str,
    wrapSummaryCheck: Optional[Callable[[MLInst], Tuple[Expr, List[Expr]]]] = None,
    fnNameSuffix: str = "",
    uninterpFuncs: List[str] = [],
    log: bool = True,
) -> Tuple[Set[Var], List[Synth], List[Expr], Expr, List[CodeInfo]]:
    with open(filename, mode="r") as file:
        ref = llvm.parse_assembly(file.read())

    fn = ref.get_function(fnName)
    blocksMap = setupBlocks(fn.blocks)

    parseSrets(list(fn.arguments), blocksMap.values())
    globalVars = parseGlobals(ref.global_variables, log=log)
    parseObjectFuncs(blocksMap)

    loops = parseLoops(loopsFile, fnName, log=log)
    loopAndPsInfo = []
    for l in loops:
        # assume for now there is only one header block
        if len(l.header) > 1:
            raise Exception("multiple loop headers: %s" % l)  # type: ignore
        loopAndPsInfo.append(
            processLoops(
                blocksMap[l.header[0]],
                [blocksMap[n] for n in l.body],
                [blocksMap[n] for n in l.exits],
                [blocksMap[n] for n in l.latches],
                list(fn.arguments),
            )
        )

    # add ps code info
    loopAndPsInfo = loopAndPsInfo + processBranches(
        blocksMap, list(fn.arguments), wrapSummaryCheck, fnName
    )

    if log:
        print("====== after transforms")

        for b in blocksMap.values():
            print("blk: %s" % b.name)
            for i in b.instructions:
                print("%s" % i)

        print("====== compute vc")

    (vars, invAndPs, preds, vc) = VC(fnName + fnNameSuffix, log=log).computeVC(
        blocksMap,
        list(fn.blocks)[0].name,
        list(fn.arguments),
        globalVars,
        uninterpFuncs,
    )

    return (vars, invAndPs, preds, vc, loopAndPsInfo)


def format_with_index(a: str, idx: int) -> str:
    if idx == 0:
        return a
    else:
        return f"{a}_{idx}"


class VariableTracker(object):
    groups: Dict[str, int]
    existing: Dict[str, int]
    var_to_type: Dict[str, ObjectT]

    def __init__(self) -> None:
        self.groups = {}
        self.existing = {}
        self.var_to_type = {}
        return

    def group(self, name: str) -> "VariableGroup":
        if name in self.groups:
            self.groups[name] += 1
        else:
            self.groups[name] = 0
        return VariableGroup(self, format_with_index(name, self.groups[name]))

    def variable(self, name: str, type: ObjectT) -> Var:
        self.var_to_type[name] = type
        return Var(name, type)

    def all(self) -> List[Var]:
        return [Var(name, self.var_to_type[name]) for name in self.var_to_type]


class VariableGroup(object):
    def __init__(self, tracker: VariableTracker, name: str):
        self.tracker = tracker
        self.name = name

    def existing_variable(self, name: str, type: ObjectT) -> Var:
        my_name = f"{self.name}_{name}"

        if my_name not in self.tracker.existing:
            raise Exception(f"Variable {my_name} does not exist")
        else:
            if self.tracker.existing[my_name] > 0:
                raise Exception(f"There are multiple instances of variable {my_name}")

        assert (
            self.tracker.var_to_type[
                format_with_index(my_name, self.tracker.existing[my_name])
            ]
            == type
        )
        return Var(format_with_index(my_name, self.tracker.existing[my_name]), type)

    def variable_or_existing(self, name: str, type: ObjectT) -> Var:
        my_name = f"{self.name}_{name}"
        if my_name not in self.tracker.existing:
            self.tracker.existing[my_name] = 0
            self.tracker.var_to_type[
                format_with_index(my_name, self.tracker.existing[my_name])
            ] = type
        else:
            if self.tracker.existing[my_name] > 0:
                raise Exception(f"There are multiple instances of variable {my_name}")

        assert (
            self.tracker.var_to_type[
                format_with_index(my_name, self.tracker.existing[my_name])
            ]
            == type
        )
        return Var(format_with_index(my_name, self.tracker.existing[my_name]), type)

    def variable(self, name: str, type: ObjectT) -> Var:
        my_name = f"{self.name}_{name}"
        if my_name in self.tracker.existing:
            self.tracker.existing[my_name] += 1
        else:
            self.tracker.existing[my_name] = 0

        self.tracker.var_to_type[
            format_with_index(my_name, self.tracker.existing[my_name])
        ] = type
        return Var(format_with_index(my_name, self.tracker.existing[my_name]), type)

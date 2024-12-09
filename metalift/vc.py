import re
import typing
from collections import defaultdict
from copy import deepcopy
from typing import Any, Dict, Optional, Union

from llvmlite.binding import TypeRef, ValueRef

from metalift import models, vc_util
from metalift.ir import (
    Add,
    And,
    Bool,
    BoolLit,
    Call,
    Eq,
    Expr,
    Implies,
    Int,
    IntLit,
    Ite,
    Le,
)
from metalift.ir import List as mlList
from metalift.ir import Lit, Lt, MLInst, Mul, Not, Object, ObjectT, Or
from metalift.ir import Set as mlSet
from metalift.ir import Sub, Synth, Var, make_tuple_type, parse_type_ref_to_obj


class State:
    regs: Dict[ValueRef, Expr]
    mem: Dict[ValueRef, Expr]
    args: typing.List[Expr]
    vc: Optional[Expr]
    assumes: typing.List[Expr]
    uninterpFuncs: typing.List[str]
    gvars: Dict[str, str]

    def __init__(self) -> None:
        self.regs = {}
        self.mem = {}
        self.args = []
        self.vc = None
        self.assumes = []
        self.uninterpFuncs = []
        self.gvars = {}

    def __repr__(self) -> str:
        # keys are ValueRef objs
        return "regs: %s\nmem: %s\nvc: %s\n" % (
            ", ".join(["%s: %s" % (k.name, v) for (k, v) in self.regs.items()]),
            ", ".join(["%s: %s" % (k.name, v) for (k, v) in self.mem.items()]),
            self.vc,
        )


class Block:
    regs: Dict[ValueRef, Expr]
    preds: typing.List[Any]
    succs: typing.List[Any]

    def __init__(self, name: str, instructions: typing.List[ValueRef]) -> None:
        self.name = name
        self.instructions = instructions
        self.preds = []
        self.succs = []
        self.state = State()

    def __repr__(self) -> str:
        return "name: %s, pred: %s, succ: %s" % (
            self.name,
            ",".join([p.name for p in self.preds]),
            ",".join([s.name for s in self.succs]),
        )


class VC:
    preds: Dict[str, Expr]
    vars: typing.Set[Var]
    log: bool

    def __init__(self, fnName: str = "ps", log: bool = True) -> None:
        self.vars = set()
        self.havocNum = 0
        self.preds = dict()
        self.fnName = fnName
        self.log = log

    def makeVar(self, name: str, ty: Union[TypeRef, ObjectT]) -> Expr:
        if isinstance(ty, TypeRef):
            ty = parse_type_ref_to_obj(ty)
        elif isinstance(ty, Object):
            pass
        else:
            raise Exception("NYI %s with type %s" % (name, ty))

        e = Var(self.fnName + "_" + name, ty)
        found = any(v.args[0] == e.args[0] and v.type == ty for v in self.vars)
        if not found:
            self.vars.add(e)

        return e

    def callPred(self, name: str, returnT: ObjectT, *args: Expr) -> Expr:
        newArgs = [Var("v%s" % i, a.type) for (i, a) in zip(range(len(args)), args)]
        self.preds[name] = Call(name, returnT, *newArgs)
        return Call(name, returnT, *args)

    def computeVC(
        self,
        blocksMap: Dict[str, Block],
        firstBlockName: str,
        arguments: typing.List[ValueRef],
        gvars: Dict[str, str],
        uninterpFuncs: typing.List[str] = [],
    ) -> tuple[typing.Set[Var], typing.List[Synth], typing.List[Expr], Expr]:
        initBlock = blocksMap[firstBlockName]
        initBlock.state.assumes.append(BoolLit(True))
        initBlock.state.gvars = gvars
        for arg in arguments:
            v = self.makeVar(arg.name, arg.type)
            initBlock.state.regs[arg] = v
            initBlock.state.args.append(v)
            initBlock.state.assumes.append(BoolLit(True))
            initBlock.state.uninterpFuncs.extend(uninterpFuncs)

        # simple loop assuming the blocks are in predecessor order
        # for b in blocksMap.values():
        #  self.compute(b)

        # worklist style loop that doesn't assume any ordering of the blocks
        done = False
        while not done:
            done = True
            for b in blocksMap.values():
                if b.state.vc is None and (
                    not b.preds or all([p.state.vc is not None for p in b.preds])
                ):
                    self.compute(b)
                    done = False

        sorted_values = list(blocksMap.values())
        sorted_values.sort(key=lambda b: b.name)
        blockVCs: ListT[Expr] = [b.state.vc for b in sorted_values]  # type: ignore

        body = Implies(And(*blockVCs), self.makeVar(firstBlockName, Bool))

        invAndPs = [
            Synth(p.args[0], Lit(True, Bool), *p.args[1:])
            for p in filter(
                lambda p: p.args[0] == "ps" or p.args[0].startswith("inv"),
                self.preds.values(),
            )
        ]
        preds = list(
            filter(
                lambda p: not (p.args[0] == "ps" or p.args[0].startswith("inv")),
                self.preds.values(),
            )
        )

        return self.vars, invAndPs, preds, body

    # merge either the registers or mem dict passed in containers
    def merge(
        self,
        containers: typing.List[tuple[str, typing.List[Expr], Dict[ValueRef, Expr]]],
    ) -> Dict[ValueRef, Expr]:
        groups: Dict[
            ValueRef, Dict[Expr, typing.List[typing.List[Expr]]]
        ] = defaultdict(lambda: defaultdict(list))
        for pname, path, container in containers:
            for k, v in container.items():
                # groups[k][v].append(self.makeVar(pname, bool))
                groups[k][v].append(path)

        merged = dict()
        for k, vals in groups.items():
            if len(vals) == 1:
                merged[k] = list(vals.keys())[0]
            else:
                valPaths = dict()
                for v in vals:
                    paths = [
                        And(*pathStack) if len(pathStack) > 1 else pathStack[0]
                        for pathStack in vals[v]
                    ]
                    valPaths[v] = Or(*paths) if len(paths) > 1 else paths[0]

                e = list(valPaths.items())[0][0]
                for vp in list(valPaths.items())[1:]:
                    e = Ite(vp[1], vp[0], e)

                merged[k] = e
                if self.log:
                    print("merged[%s] = %s" % (k.name, e))

        return merged

    def mergeStates(self, preds: typing.List[Block]) -> State:
        if len(preds) == 1:
            s = State()
            src = preds[0].state
            s.regs = dict([(k, deepcopy(v)) for k, v in src.regs.items()])
            s.mem = dict([(k, deepcopy(v)) for k, v in src.mem.items()])
            s.args = deepcopy(src.args)
            s.assumes = deepcopy(src.assumes)
            s.uninterpFuncs = deepcopy(src.uninterpFuncs)
            s.gvars = deepcopy(src.gvars)
            return s

        else:  # merge
            s = State()
            s.regs = self.merge(
                [(p.name, p.state.assumes, p.state.regs) for p in preds]
            )
            s.mem = self.merge([(p.name, p.state.assumes, p.state.mem) for p in preds])

            s.args = preds[0].state.args

            # vc should be None

            assumeE = [
                And(*p.state.assumes)
                if len(p.state.assumes) > 1
                else p.state.assumes[0]
                for p in preds
            ]
            s.assumes.append(Or(*assumeE) if len(assumeE) > 1 else assumeE[0])

            if any(
                p.state.uninterpFuncs != preds[0].state.uninterpFuncs for p in preds
            ):
                raise Exception(
                    "preds have different number of uninterpreted functions: %s"
                    % "; ".join([str(p.state.uninterpFuncs) for p in preds])
                )
            s.uninterpFuncs.extend(preds[0].state.uninterpFuncs)

            if all(p.state.gvars == preds[0].state.gvars for p in preds):
                s.gvars = preds[0].state.gvars

            else:
                raise Exception(
                    "globals are not the same in states to be merged: %s" % str(preds)
                )

            return s

    def formVC(
        self,
        blockName: str,
        regs: Dict[ValueRef, Expr],
        assigns: typing.Set[ValueRef],
        assumes: typing.List[Expr],
        asserts: typing.List[Union[Any, Expr]],
        succs: typing.List[Union[Any, Block]],
    ) -> Expr:
        # concat all assignments
        if not assigns:
            assignE: Optional[Expr] = None
        elif len(assigns) == 1:  # r1 = v1
            a = list(assigns)[0]
            assignE = Eq(self.makeVar(a.name, a.type), regs[a])
        else:  # r1 = v1 and r2 = v2 ...
            sorted_assigns = list(assigns)
            sorted_assigns.sort(key=lambda a: a.name)
            assignE = And(
                *[Eq(self.makeVar(r.name, r.type), regs[r]) for r in sorted_assigns]
            )

        if not assumes:
            assumeE = None
        elif len(assumes) == 1:
            assumeE = assumes[0]
        else:
            assumeE = And(*assumes)

        if not assignE and not assumeE:
            lhs: Optional[Expr] = None
        elif assignE and not assumeE:
            lhs = assignE
        elif not assignE and assumeE:
            lhs = assumeE
        else:
            lhs = And(assignE, assumeE)  # type: ignore

        if not succs:
            succE = None
        elif len(succs) == 1:
            succE = self.makeVar(succs[0].name, Bool)
        else:
            succE = And(*[self.makeVar(s.name, Bool) for s in succs])

        if not asserts:
            assertE = None
        elif len(asserts) == 1:
            assertE = asserts[0]
        else:
            assertE = And(*asserts)

        if not succE and not assertE:
            rhs = None
        elif succE and not assertE:
            rhs = succE
        elif not succE and assertE:
            rhs = assertE
        else:
            rhs = And(succE, assertE)  # type: ignore

        vc = Eq(
            self.makeVar(blockName, Bool),
            rhs if not lhs else Implies(lhs, rhs),  # type: ignore
        )

        return vc

    def compute(self, b: Block) -> State:
        s = self.mergeStates(b.preds) if b.preds else b.state
        assigns = set()
        asserts = list()

        if self.log:
            print("block: %s" % b.name)
        for i in b.instructions:
            if self.log:
                print("inst: %s" % i)

            opcode = i.opcode
            ops = list(i.operands)

            if opcode == "alloca":
                # alloca <type>, align <num> or alloca <type>
                t = re.search("alloca ([^$|,]+)", str(i)).group(  # type: ignore
                    1
                )  # bug: ops[0] always return i32 1 regardless of type
                if t == "i32":
                    s.mem[i] = Lit(0, Int)
                elif t == "i8":
                    s.mem[i] = Lit(False, Bool)
                elif t == "i1":
                    s.mem[i] = Lit(False, Bool)
                elif t == "%struct.list*":
                    s.mem[i] = Lit(0, mlList[Int])
                elif t.startswith("%struct.set"):
                    s.mem[i] = Lit(0, mlSet[Int])
                elif t.startswith("%struct.tup."):
                    retType = [Int for i in range(int(t[-2]) + 1)]
                    s.mem[i] = Lit(0, make_tuple_type(*retType))
                elif t.startswith("%struct.tup"):
                    s.mem[i] = Lit(0, make_tuple_type(Int, Int))
                # TODO: see how to handle user defined structs
                # elif t.startswith(
                #     "%struct."
                # ):  # not a tuple or set, assume to be user defined type
                #     o = re.search("%struct.(.+)", t)
                #     if o:
                #         tname = o.group(1)
                #     else:
                #         raise Exception("failed to match struct %s: " % t)

                #     s.mem[i] = ObjectExpr(Type(tname))
                else:
                    raise Exception("NYI: %s" % i)

            elif opcode == "load":
                s.regs[i] = s.mem[ops[0]]
                assigns.add(i)

            elif opcode == "store":
                # store either a reg or a literal
                s.mem[ops[1]] = VC.parse_operand(ops[0], s.regs)

            elif opcode in ("add", "sub", "mul"):
                op1 = VC.parse_operand(ops[0], s.regs)
                op2 = VC.parse_operand(ops[1], s.regs)
                if opcode == "add":
                    s.regs[i] = Add(op1, op2)
                elif opcode == "sub":
                    s.regs[i] = Sub(op1, op2)
                elif opcode == "mul":
                    s.regs[i] = Mul(op1, op2)

            elif opcode == "icmp":
                cond = re.match("\S+ = icmp (\w+) \S+ \S+ \S+", str(i).strip()).group(1)  # type: ignore
                op1 = VC.parse_operand(ops[0], s.regs)
                op2 = VC.parse_operand(ops[1], s.regs)

                if cond == "eq":
                    r: Expr = Eq(op2, op1)
                elif cond == "ne":
                    r = Not(Eq(op2, op1))
                elif cond == "sgt":
                    r = Lt(op2, op1)
                elif cond == "sle":
                    r = Le(op1, op2)
                elif cond == "slt" or cond == "ult":
                    r = Lt(op1, op2)
                else:
                    raise Exception("NYI %s" % cond)

                s.regs[i] = r
                assigns.add(i)

            elif opcode == "br" or opcode == "ret" or opcode == "switch":
                pass

            elif opcode == "bitcast" or opcode == "sext":
                # XXX: this is a hack. bitcast should operate on reg values.
                # this is because we currently do not assign out numerical addresses that are stored in regs
                if ops[0] in s.regs:
                    s.regs[i] = VC.parse_operand(ops[0], s.regs)
                else:
                    s.mem[i] = VC.parse_operand(ops[0], s.mem)

            elif opcode == "call":  # last arg is fn to be called
                fnName = ops[-1] if isinstance(ops[-1], str) else ops[-1].name
                if fnName == "":
                    # TODO: this is a hack around LLVM bitcasting the function before calling it on aarch64
                    fnName = str(ops[-1]).split("@")[-1].split(" ")[0]
                if fnName in models.fn_models:
                    rv = models.fn_models[fnName](s.regs, s.mem, s.gvars, *ops[:-1])
                    if rv.val:
                        s.regs[i] = rv.val.src
                        assigns.add(i)
                    if rv.assigns:
                        for k, v, _ in rv.assigns:
                            s.regs[k] = v.src
                            assigns.add(k)

                elif fnName in s.uninterpFuncs:
                    s.regs[i] = Call(
                        fnName,
                        parse_type_ref_to_obj(i.type),
                        *[s.regs[op] for op in ops[:-1]],
                    )
                    assigns.add(i)

                # elif fnName == "setField":
                #     (fieldName, obj, val, fname) = ops
                #     print("%s %s to %s" % (fname, obj, val))
                #     s.mem[obj].args[fieldName.args[0]] = s.regs[val]
                #
                # elif fnName == "getField":
                #     (fieldName, obj, fname) = ops
                #     print("get %s %s" % (fname, s.mem[obj].args[fieldName.args[0]]))
                #     s.regs[i] = s.mem[obj].args[fieldName.args[0]]
                #     print("get to %s %s" % (i, s.regs[i]))

                else:
                    raise Exception("NYI: %s, name: %s" % (i, fnName))

            elif opcode == "assert":
                e = VC.evalMLInst(ops[0], s.regs, s.mem)
                # e = ops[0]
                # if e.opcode == "call":
                #   name = e.operands[-1]
                #   if name.startswith("inv"):
                #     parsed = [VC.evalMLInst(arg, s.regs, s.mem) for arg in e.operands[0:-1]]
                #     e = self.callPred(name, Bool(), *parsed)
                #     #parsed = VC.parseExpr(e, s.regs, s.mem)
                #     #e = self.callPred(parsed.args[0], parsed.type, *parsed.args[1:])
                #
                #   elif name == "ps":
                #     parsed = [VC.evalMLInst(arg, s.regs, s.mem) for arg in e.operands[0:-1]]
                #     e = self.callPred(name, Bool(), *parsed)
                #
                #     # parsed = VC.evalMLInst(e, s.regs, s.mem)
                #     # e = self.callPred(parsed.args[0], parsed.type, *parsed.args[1:])
                #   else: raise Exception("NYI: %s" % i)
                # else: raise Exception("NYI: %s" % i)

                asserts.append(e)

            elif opcode == "assume":
                s.assumes.append(VC.evalMLInst(ops[0], s.regs, s.mem))  # type: ignore
                # if isinstance(ops[0], MLInstruction):
                #   s.assumes.append(VC.evalMLInst(ops[0], s.regs, s.mem))
                # elif isinstance(ops[0], ValueRef):
                #   s.assumes.append(VC.parse_operand(ops[0], s.regs))
                # else: raise Exception("NYI: %s" % i)

            elif opcode == "havoc":
                for op in ops:
                    s.mem[op] = self.makeVar(
                        "%s_%s" % (op.name, self.havocNum), s.mem[op].type
                    )
                    self.havocNum = self.havocNum + 1

            else:
                raise Exception("NYI: %s" % i)

        s.vc = self.formVC(b.name, s.regs, assigns, s.assumes, asserts, b.succs)

        if self.log:
            print("final state: %s" % s)
        b.state = s
        return s

    # evaluate a ML instruction. returns an IR Expr
    @staticmethod
    def evalMLInst(
        i: Union[ValueRef, MLInst, str, Expr],
        reg: Dict[ValueRef, Expr],
        mem: Dict[ValueRef, Expr],
    ) -> Union[str, ValueRef, Expr]:
        # TODO: fix this hack
        if isinstance(i, ValueRef) and str(i) == "i32 0":
            return IntLit(0)
        if isinstance(i, ValueRef):
            return reg[i]
        if isinstance(i, Expr):
            if isinstance(i, Lit):
                return i
            else:
                return i.map_args(lambda x: VC.evalMLInst(x, reg, mem))  # type: ignore
        elif isinstance(i, str):
            return i
        elif i.opcode == "load":
            return mem[i.operands[0]]
        elif i.opcode == "not":
            return Not(VC.evalMLInst(i.operands[0], reg, mem))  # type: ignore
        elif i.opcode == "or":
            return Or(VC.evalMLInst(i.operands[0], reg, mem))  # type: ignore
        elif i.opcode == "call":
            return Call(
                i.operands[0],  # type: ignore
                i.operands[1],  # type: ignore
                *[VC.evalMLInst(a, reg, mem) for a in i.operands[2:]],  # type: ignore
            )
        else:
            raise Exception("NYI: %s" % i)

    @staticmethod
    def parse_operand(
        op: ValueRef, reg: Dict[ValueRef, Expr], hasType: bool = True
    ) -> Expr:
        return vc_util.parse_operand(op, reg, hasType)

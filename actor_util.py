import sys
import os

from analysis import CodeInfo, analyze
import ir
from ir import *
from smt_util import toSMT

from llvmlite.binding import ValueRef

import typing
from typing import Callable, Union, Protocol


def observeEquivalence(inputState: Expr, synthState: Expr) -> Expr:
    return Call("equivalence", Bool(), inputState, synthState)


class SynthesizeFun(Protocol):
    def __call__(
        self,
        basename: str,
        targetLang: typing.List[Expr],
        vars: typing.Set[Expr],
        invAndPs: typing.List[Expr],
        preds: Union[str, typing.List[Expr]],
        vc: Expr,
        loopAndPsInfo: typing.List[Union[CodeInfo, Expr]],
        cvcPath: str,
        noVerify: bool = False,
        unboundedInts: bool = False,
    ) -> typing.List[Expr]:
        ...

def check_aci():
    filename = sys.argv[1]
    basename = os.path.splitext(os.path.basename(filename))[0]

    fnNameBase = sys.argv[2]
    loopsFile = sys.argv[3]
    cvcPath = sys.argv[4]

    # begin state transition
    wrapBeforeState = None
    wrapAfterState = None
    wrapTransitionArgs = None
    nextVc = None

    def summaryWrapStateTransition(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        nonlocal wrapBeforeState
        nonlocal wrapAfterState
        nonlocal wrapTransitionArgs
        nonlocal nextVc

        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]
        wrapTransitionArgs = origArgs[1:]

        beforeState = typing.cast(ValueRef, origArgs[0])
        afterState = typing.cast(ValueRef, origReturn)

        prevAfterState = wrapAfterState

        wrapBeforeState = beforeState
        wrapAfterState = afterState

        if not nextVc:
            finalState_0 = Var(fnNameBase + "_next_state" + "_0_cmd1_" + wrapAfterState.name, parseTypeRef(wrapAfterState.type))
            finalState_1 = Var(fnNameBase + "_next_state" + "_1_cmd1_" + wrapAfterState.name, parseTypeRef(wrapAfterState.type))
            nextVc = Eq(finalState_0, finalState_1)

        return (
            Implies(Eq(prevAfterState, beforeState), nextVc) if prevAfterState else nextVc,
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsStateTransition_0_cmd0,
        invAndPsStateTransition_0_cmd0,
        predsStateTransition_0_cmd0,
        nextVc,
        loopAndPsInfoStateTransition_0_cmd0,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_0_cmd0"
    )

    beforeState_0_cmd0 = Var(fnNameBase + "_next_state" + "_0_cmd0_" + wrapBeforeState.name, parseTypeRef(wrapBeforeState.type))
    wrapAfterState = Var(fnNameBase + "_next_state" + "_0_cmd0_" + wrapAfterState.name, parseTypeRef(wrapAfterState.type))
    afterState_0_cmd0 = wrapAfterState
    transitionArgs_0_cmd0 = [Var(fnNameBase + "_next_state" + "_0_cmd0_" + v.name, parseTypeRef(v.type)) for v in wrapTransitionArgs]

    (
        vcVarsStateTransition_0_cmd1,
        invAndPsStateTransition_0_cmd1,
        predsStateTransition_0_cmd1,
        nextVc,
        loopAndPsInfoStateTransition_0_cmd1,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_0_cmd1"
    )

    beforeState_0_cmd1 = Var(fnNameBase + "_next_state" + "_0_cmd1_" + wrapBeforeState.name, parseTypeRef(wrapBeforeState.type))
    wrapAfterState = Var(fnNameBase + "_next_state" + "_0_cmd1_" + wrapAfterState.name, parseTypeRef(wrapAfterState.type))
    afterState_0_cmd1 = wrapAfterState
    transitionArgs_0_cmd1 = [Var(fnNameBase + "_next_state" + "_0_cmd1_" + v.name, parseTypeRef(v.type)) for v in wrapTransitionArgs]

    wrapAfterState = None

    (
        vcVarsStateTransition_1_cmd0,
        invAndPsStateTransition_1_cmd0,
        predsStateTransition_1_cmd0,
        nextVc,
        loopAndPsInfoStateTransition_1_cmd0,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_1_cmd0"
    )

    beforeState_1_cmd0 = Var(fnNameBase + "_next_state" + "_1_cmd0_" + wrapBeforeState.name, parseTypeRef(wrapBeforeState.type))
    wrapAfterState = Var(fnNameBase + "_next_state" + "_1_cmd0_" + wrapAfterState.name, parseTypeRef(wrapAfterState.type))
    afterState_1_cmd0 = wrapAfterState
    transitionArgs_1_cmd0 = [Var(fnNameBase + "_next_state" + "_1_cmd0_" + v.name, parseTypeRef(v.type)) for v in wrapTransitionArgs]

    (
        vcVarsStateTransition_1_cmd1,
        invAndPsStateTransition_1_cmd1,
        predsStateTransition_1_cmd1,
        nextVc,
        loopAndPsInfoStateTransition_1_cmd1,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_1_cmd1"
    )

    beforeState_1_cmd1 = Var(fnNameBase + "_next_state" + "_1_cmd1_" + wrapBeforeState.name, parseTypeRef(wrapBeforeState.type))
    wrapAfterState = Var(fnNameBase + "_next_state" + "_1_cmd1_" + wrapAfterState.name, parseTypeRef(wrapAfterState.type))
    afterState_1_cmd1 = wrapAfterState
    transitionArgs_1_cmd1 = [Var(fnNameBase + "_next_state" + "_1_cmd1_" + v.name, parseTypeRef(v.type)) for v in wrapTransitionArgs]

    combinedVCVars = vcVarsStateTransition_0_cmd0.union(vcVarsStateTransition_0_cmd1).union(vcVarsStateTransition_1_cmd0).union(vcVarsStateTransition_1_cmd1)

    combinedInvAndPs = (
        invAndPsStateTransition_0_cmd0
        + invAndPsStateTransition_0_cmd1
        + invAndPsStateTransition_1_cmd0
        + invAndPsStateTransition_1_cmd1
    )

    combinedPreds = predsStateTransition_0_cmd0 + predsStateTransition_0_cmd1 + predsStateTransition_1_cmd0 + predsStateTransition_1_cmd1

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransition_0_cmd0
        + loopAndPsInfoStateTransition_0_cmd1
        + loopAndPsInfoStateTransition_1_cmd0
        + loopAndPsInfoStateTransition_1_cmd1
    )

    combinedVC = Implies(
        And(
            Eq(beforeState_0_cmd0, beforeState_1_cmd0),
            And(
                *[
                    Eq(a1, a2)
                    for a1, a2 in zip(transitionArgs_0_cmd0, transitionArgs_1_cmd1)
                ]
            ),
            And(
                *[
                    Eq(a1, a2)
                    for a1, a2 in zip(transitionArgs_0_cmd1, transitionArgs_1_cmd0)
                ]
            )
        ),
        nextVc
    )
    # end state transition

    ir.printMode = PrintMode.SMT
    toSMT([], combinedVCVars, [], combinedPreds, combinedVC, "test.smt", [], [])
    print(beforeState_0_cmd0)
    print(beforeState_1_cmd0)

    print(afterState_0_cmd0)
    print(afterState_1_cmd0)

    print(beforeState_0_cmd1)
    print(beforeState_1_cmd1)

    print(afterState_0_cmd1)
    print(afterState_1_cmd1)

    print(transitionArgs_0_cmd0)
    print(transitionArgs_0_cmd1)
    print(transitionArgs_1_cmd0)
    print(transitionArgs_1_cmd1)

    # print(afterState_0)
    # print(beforeState_1)
    # print(afterState_1)
    # print(transitionArgs_0)
    # print(transitionArgs_1)

def synthesize_actor(
    synthStateType: Type,
    initState: Callable[[], Expr],
    grammarStateInvariant: Callable[[Expr], Expr],
    supportedCommand: Callable[[Expr, Expr, typing.Any], Expr],
    grammar: Callable[[CodeInfo], Expr],
    grammarQuery: Callable[[CodeInfo], Expr],
    grammarEquivalence: Callable[[Expr, Expr], Expr],
    targetLang: Callable[[], typing.List[Expr]],
    synthesize: SynthesizeFun,
) -> typing.List[Expr]:
    filename = sys.argv[1]
    basename = os.path.splitext(os.path.basename(filename))[0]

    fnNameBase = sys.argv[2]
    loopsFile = sys.argv[3]
    cvcPath = sys.argv[4]

    # begin state transition
    extraVarsStateTransition = set()
    stateType = None

    def summaryWrapStateTransition(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        nonlocal stateType

        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        beforeState = typing.cast(ValueRef, origArgs[0])
        afterState = typing.cast(ValueRef, origReturn)

        stateType = parseTypeRef(beforeState.type)

        beforeStateForPS = Var(beforeState.name + "_for_ps", synthStateType)
        extraVarsStateTransition.add(beforeStateForPS)

        afterStateForPS = Var(afterState.name + "_for_ps", synthStateType)
        extraVarsStateTransition.add(afterStateForPS)

        newReturn = afterStateForPS

        newArgs = list(origArgs)
        newArgs[0] = beforeStateForPS

        ps.operands = tuple(list(ps.operands[:2]) + [newReturn] + newArgs)

        return (
            Implies(
                And(
                    supportedCommand(beforeState, beforeStateForPS, origArgs[1:]),
                    observeEquivalence(beforeState, beforeStateForPS),
                ),
                Implies(
                    ps,
                    observeEquivalence(afterState, afterStateForPS),
                ),
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsStateTransition,
        invAndPsStateTransition,
        predsStateTransition,
        vcStateTransition,
        loopAndPsInfoStateTransition,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
    )

    vcVarsStateTransition = vcVarsStateTransition.union(extraVarsStateTransition)
    invAndPsStateTransition = [grammar(ci) for ci in loopAndPsInfoStateTransition]
    # end state transition

    # begin query
    extraVarsQuery = set()

    def summaryWrapQuery(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        beforeState = typing.cast(ValueRef, origArgs[0])

        beforeStateForQuery = Var(beforeState.name + "_for_query", synthStateType)
        extraVarsQuery.add(beforeStateForQuery)

        newArgs = list(origArgs)
        newArgs[0] = beforeStateForQuery

        ps.operands = tuple(list(ps.operands[:2]) + [origReturn] + newArgs)

        return (
            Implies(
                observeEquivalence(beforeState, beforeStateForQuery),
                ps,
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (vcVarsQuery, invAndPsQuery, predsQuery, vcQuery, loopAndPsInfoQuery) = analyze(
        filename, fnNameBase + "_response", loopsFile, wrapSummaryCheck=summaryWrapQuery
    )

    vcVarsQuery = vcVarsQuery.union(extraVarsQuery)
    invAndPsQuery = [grammarQuery(ci) for ci in loopAndPsInfoQuery]
    # end query

    # begin init state
    extraVarsInitState = set()

    def summaryWrapInitState(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]

        afterState = typing.cast(ValueRef, origReturn)

        afterStateForInitState = Var(
            afterState.name + "_for_init_state", synthStateType
        )
        extraVarsInitState.add(afterStateForInitState)

        newReturn = afterStateForInitState

        ps.operands = tuple(list(ps.operands[:2]) + [newReturn])

        return (
            Implies(
                Eq(afterStateForInitState, initState()),
                observeEquivalence(afterState, afterStateForInitState),
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsInitState,
        invAndPsInitState,
        predsInitState,
        vcInitState,
        loopAndPsInfoInitState,
    ) = analyze(
        filename,
        fnNameBase + "_init_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapInitState,
    )

    vcVarsInitState = vcVarsInitState.union(extraVarsInitState)
    loopAndPsInfoInitState = []
    invAndPsInitState = []
    # end init state

    # begin equivalence
    inputStateForEquivalence = Var("inputState", stateType)  # type: ignore
    synthStateForEquivalence = Var("synthState", synthStateType)

    invAndPsEquivalence = [
        Synth(
            "equivalence",
            And(
                grammarEquivalence(inputStateForEquivalence, synthStateForEquivalence),
                grammarStateInvariant(synthStateForEquivalence),
            ),
            inputStateForEquivalence,
            synthStateForEquivalence,
        )
    ]
    # end equivalence

    print("====== synthesis")

    combinedVCVars = vcVarsStateTransition.union(vcVarsQuery).union(vcVarsInitState)

    combinedInvAndPs = (
        invAndPsStateTransition
        + invAndPsQuery
        + invAndPsInitState
        + invAndPsEquivalence
    )

    combinedPreds = predsStateTransition + predsQuery + predsInitState

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransition
        + loopAndPsInfoQuery
        + loopAndPsInfoInitState
        + invAndPsEquivalence  # type: ignore
    )
    combinedVC = And(vcStateTransition, vcQuery, vcInitState)

    lang = targetLang()

    return synthesize(
        basename,
        lang,
        combinedVCVars,
        combinedInvAndPs,
        combinedPreds,
        combinedVC,
        combinedLoopAndPsInfo,
        cvcPath,
        unboundedInts=True,
    )

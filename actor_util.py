import sys
import os

from analysis import CodeInfo, analyze
from ir import *

from llvmlite.binding import ValueRef

import typing
from typing import Callable, Union, Protocol


def observeEquivalence(inputState: Expr, synthState: Expr) -> Expr:
    return Call("equivalence", Bool(), inputState, synthState)


def stateInvariant(synthState: Expr) -> Expr:
    return Call("stateInvariant", Bool(), synthState)


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
                    stateInvariant(beforeStateForPS),
                    And(
                        supportedCommand(beforeState, beforeStateForPS, origArgs[1:]),
                        observeEquivalence(beforeState, beforeStateForPS),
                    ),
                ),
                Implies(
                    ps,
                    And(
                        stateInvariant(afterStateForPS),
                        observeEquivalence(afterState, afterStateForPS),
                    ),
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
                And(
                    stateInvariant(beforeStateForQuery),
                    observeEquivalence(beforeState, beforeStateForQuery),
                ),
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

        afterStateForInitState = Var(afterState.name + "_for_init_state", synthStateType)
        extraVarsInitState.add(afterStateForInitState)

        newReturn = afterStateForInitState

        ps.operands = tuple(list(ps.operands[:2]) + [newReturn])

        return (
            Implies(
                Eq(
                    afterStateForInitState,
                    initState()
                ),
                And(
                    stateInvariant(afterStateForInitState),
                    observeEquivalence(afterState, afterStateForInitState),
                ),
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (vcVarsInitState, invAndPsInitState, predsInitState, vcInitState, loopAndPsInfoInitState) = analyze(
        filename, fnNameBase + "_init_state", loopsFile, wrapSummaryCheck=summaryWrapInitState
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
            grammarEquivalence(inputStateForEquivalence, synthStateForEquivalence),
            inputStateForEquivalence,
            synthStateForEquivalence,
        )
    ]
    # end equivalence

    # begin state invariant
    synthStateForInvariant = Var("synthState", synthStateType)
    invAndPsStateInvariant = [
        Synth(
            "stateInvariant",
            grammarStateInvariant(synthStateForInvariant),
            synthStateForInvariant,
        )
    ]
    # end state invariant

    print("====== synthesis")

    combinedVCVars = vcVarsStateTransition.union(vcVarsQuery).union(vcVarsInitState)

    combinedInvAndPs = (
        invAndPsStateTransition
        + invAndPsQuery
        + invAndPsInitState
        + invAndPsEquivalence
        + invAndPsStateInvariant
    )

    combinedPreds = predsStateTransition + predsQuery + predsInitState

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransition
        + loopAndPsInfoQuery
        + loopAndPsInfoInitState
        + invAndPsEquivalence  # type: ignore
        + invAndPsStateInvariant  # type: ignore
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

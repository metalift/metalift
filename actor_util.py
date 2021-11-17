import sys
import os

from analysis import CodeInfo, analyze
from ir import *

from llvmlite.binding import ValueRef

import typing
from typing import Callable, Union


def observeEquivalence(inputState: Expr, synthState: Expr) -> Expr:
    return Call("equivalence", Bool(), inputState, synthState)


def stateInvariant(synthState: Expr) -> Expr:
    return Call("stateInvariant", Bool(), synthState)


SynthesizeFun = Callable[
    [
        str,
        typing.List[Expr],
        typing.Set[Expr],
        typing.List[Expr],
        typing.List[Expr],
        Expr,
        typing.List[Union[CodeInfo, Expr]],
        str,
    ],
    typing.List[Expr],
]


def synthesize_actor(
    synthStateType: Type,
    initState: Callable[[], Expr],
    grammarStateInvariant: Callable[[], Expr],
    supportedCommand: Callable[[Expr, ValueRef], Expr],
    grammar: Callable[[CodeInfo], Expr],
    grammarQuery: Callable[[CodeInfo], Expr],
    grammarEquivalence: Callable[[], Expr],
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

    def summaryWrapStateTransition(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        beforeState = typing.cast(ValueRef, origArgs[0])
        afterState = typing.cast(ValueRef, origReturn)

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
                        supportedCommand(beforeStateForPS, origArgs[1:]),
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
    extraVarsInitstateInvariantVC = set()
    initStateVar = Var("initState", synthStateType)
    extraVarsInitstateInvariantVC.add(initStateVar)
    initstateInvariantVC = Implies(
        Eq(initStateVar, initState()), stateInvariant(initStateVar)
    )
    # end init state

    # begin equivalence
    invAndPsEquivalence = [grammarEquivalence()]
    # end equivalence

    # begin state invariant
    invAndPsStateInvariant = [grammarStateInvariant()]
    # end state invariant

    print("====== synthesis")

    combinedVCVars = vcVarsStateTransition.union(vcVarsQuery).union(
        extraVarsInitstateInvariantVC
    )

    combinedInvAndPs = (
        invAndPsStateTransition
        + invAndPsQuery
        + invAndPsEquivalence
        + invAndPsStateInvariant
    )

    combinedPreds = predsStateTransition + predsQuery

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransition
        + loopAndPsInfoQuery
        + invAndPsEquivalence  # type: ignore
        + invAndPsStateInvariant  # type: ignore
    )
    combinedVC = And(vcStateTransition, vcQuery, initstateInvariantVC)

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
    )

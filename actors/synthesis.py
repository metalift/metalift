import os

from analysis import CodeInfo, analyze
from ir import *

from llvmlite.binding import ValueRef

import typing
from typing import Callable, Union, Protocol


def observeEquivalence(inputState: Expr, synthState: Expr) -> Expr:
    return Call("equivalence", Bool(), inputState, synthState)


def supportedCommand(synthState: Expr, args: typing.Any) -> Expr:
    return Call("supportedCommand", Bool(), synthState, *args)


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
    filename: str,
    fnNameBase: str,
    loopsFile: str,
    cvcPath: str,
    synthStateType: Type,
    initState: Callable[[], Expr],
    grammarStateInvariant: Callable[[Expr], Expr],
    grammarSupportedCommand: Callable[[Expr, typing.Any], Expr],
    inOrder: Callable[[typing.Any, typing.Any], Expr],
    grammar: Callable[[CodeInfo], Expr],
    grammarQuery: Callable[[CodeInfo], Expr],
    grammarEquivalence: Callable[[Expr, Expr], Expr],
    targetLang: Callable[[], typing.List[Expr]],
    synthesize: SynthesizeFun,
    unboundedInts: bool = False,
) -> typing.List[Expr]:
    basename = os.path.splitext(os.path.basename(filename))[0]

    # begin state transition (in order)
    extraVarsStateTransition = set()
    stateTypeOrig: Type = None  # type: ignore
    beforeStateOrigLink: Expr = None  # type: ignore
    beforeStateForPSLink: Expr = None  # type: ignore
    secondStateTransitionArgs: typing.List[Expr] = []
    op_arg_types: typing.List[Type] = []

    def summaryWrapStateTransition(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        nonlocal stateTypeOrig
        nonlocal beforeStateOrigLink
        nonlocal beforeStateForPSLink
        nonlocal secondStateTransitionArgs
        nonlocal op_arg_types

        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        for i in range(len(origArgs) - 1):
            op_arg_types.append(parseTypeRef(origArgs[i + 1].type))  # type: ignore

        secondStateTransitionArgs = [
            Var(f"second_transition_arg_{i}", parseTypeRef(origArgs[i + 1].type))  # type: ignore
            for i in range(len(origArgs) - 1)
        ]
        for arg in secondStateTransitionArgs:
            extraVarsStateTransition.add(arg)

        beforeStateOrig = typing.cast(ValueRef, origArgs[0])
        afterStateOrig = typing.cast(ValueRef, origReturn)

        stateTypeOrig = parseTypeRef(beforeStateOrig.type)

        beforeStateOrigLink = Var("before_state_orig_link", stateTypeOrig)
        extraVarsStateTransition.add(beforeStateOrigLink)

        beforeStateForPS = Var(beforeStateOrig.name + "_for_ps_2", synthStateType)
        extraVarsStateTransition.add(beforeStateForPS)
        beforeStateForPSLink = beforeStateForPS

        afterStateForPS = Var(afterStateOrig.name + "_for_ps_2", synthStateType)
        extraVarsStateTransition.add(afterStateForPS)

        newReturn = afterStateForPS

        newArgs = list(origArgs)
        newArgs[0] = beforeStateForPS

        ps.operands = tuple(list(ps.operands[:2]) + [newReturn] + newArgs)

        return (
            Implies(
                And(
                    Eq(beforeStateOrigLink, beforeStateOrig),
                    # beforeStateForPSLink = beforeStateForPS
                    And(
                        *[
                            Eq(a1, a2)  # type: ignore
                            for a1, a2 in zip(origArgs[1:], secondStateTransitionArgs)
                        ]
                    ),
                    ps,  # type: ignore
                ),
                And(
                    supportedCommand(beforeStateForPS, origArgs[1:]),
                ),
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsStateTransitionInOrder2,
        invAndPsStateTransitionInOrder2,
        predsStateTransitionInOrder2,
        vcStateTransitionInOrder2,
        loopAndPsInfoStateTransitionInOrder2,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_2",
    )

    vcVarsStateTransitionInOrder2 = vcVarsStateTransitionInOrder2.union(
        extraVarsStateTransition
    )
    invAndPsStateTransitionInOrder2 = [
        grammar(ci) for ci in loopAndPsInfoStateTransitionInOrder2
    ]

    extraVarsPriorStateTransitionInOrder = set()

    def summaryWrapPriorStateTransition(
        ps: MLInst,
    ) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        beforeStateOrig = typing.cast(ValueRef, origArgs[0])
        afterStateOrig = typing.cast(ValueRef, origReturn)

        beforeStateForPS = Var(beforeStateOrig.name + "_for_ps_prior", synthStateType)
        extraVarsPriorStateTransitionInOrder.add(beforeStateForPS)

        afterStateForPS = Var(afterStateOrig.name + "_for_ps_prior", synthStateType)
        extraVarsPriorStateTransitionInOrder.add(afterStateForPS)

        newReturn = afterStateForPS

        newArgs = list(origArgs)
        newArgs[0] = beforeStateForPS

        ps.operands = tuple(list(ps.operands[:2]) + [newReturn] + newArgs)

        return (
            Implies(
                And(
                    observeEquivalence(beforeStateOrig, beforeStateForPS),
                    Eq(afterStateOrig, beforeStateOrigLink),
                    Eq(afterStateForPS, beforeStateForPSLink),
                    supportedCommand(beforeStateForPS, origArgs[1:]),
                    ps,  # type: ignore
                ),
                And(
                    observeEquivalence(afterStateOrig, afterStateForPS),
                    Implies(
                        inOrder(origArgs[1:], secondStateTransitionArgs),
                        vcStateTransitionInOrder2,
                    ),
                ),
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsPriorStateTransitionInOrder,
        _,
        predsPriorStateTransitionInOrder,
        vcStateTransitionInOrder,
        _,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapPriorStateTransition,
        fnNameSuffix="_prior_state",
    )

    vcVarsPriorStateTransition = vcVarsPriorStateTransitionInOrder.union(
        extraVarsPriorStateTransitionInOrder
    )
    # end state transition (in order)

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

    synthInitState = Var("synth_init_state", synthStateType)

    extraVarsInitState.add(synthInitState)

    init_op_arg_vars = []
    for i, typ in enumerate(op_arg_types):
        init_op_arg_vars.append(Var(f"init_op_arg_{i}", typ))
        extraVarsInitState.add(init_op_arg_vars[-1])

    def summaryWrapInitState(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]

        returnedInitState = typing.cast(ValueRef, origReturn)

        return (
            Implies(
                And(
                    Eq(synthInitState, initState()),
                ),
                And(
                    observeEquivalence(returnedInitState, synthInitState),
                    supportedCommand(synthInitState, init_op_arg_vars),
                ),
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
    inputStateForEquivalence = Var("inputState", stateTypeOrig)
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

    synthStateForSupported = Var(f"supported_synthState", synthStateType)
    argList = [
        Var(f"supported_arg_{i}", secondStateTransitionArgs[i].type)
        for i in range(len(secondStateTransitionArgs))
    ]
    invAndPsSupported = [
        Synth(
            "supportedCommand",
            grammarSupportedCommand(synthStateForSupported, argList),
            synthStateForSupported,
            *argList,
        )
    ]
    # end equivalence

    print("====== synthesis")

    combinedVCVars = (
        vcVarsStateTransitionInOrder2.union(vcVarsPriorStateTransition)
        .union(vcVarsQuery)
        .union(vcVarsInitState)
    )

    combinedInvAndPs = (
        invAndPsStateTransitionInOrder2
        + invAndPsQuery
        + invAndPsInitState
        + invAndPsEquivalence
        + invAndPsSupported
    )

    combinedPreds = (
        predsStateTransitionInOrder2
        + predsPriorStateTransitionInOrder
        + predsQuery
        + predsInitState
    )

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransitionInOrder2
        + loopAndPsInfoQuery
        + loopAndPsInfoInitState
        + invAndPsEquivalence  # type: ignore
        + invAndPsSupported  # type: ignore
    )
    combinedVC = And(vcStateTransitionInOrder, vcQuery, vcInitState)

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
        unboundedInts=unboundedInts,
    )

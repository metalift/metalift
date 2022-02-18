import sys
import os

from analysis import CodeInfo, analyze
import ir
from ir import *
from smt_util import toSMT

from llvmlite.binding import ValueRef

import typing
from typing import Any, Callable, Union, Protocol

import subprocess
from synthesize_cvc5 import generateAST, toExpr


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


def check_aci(filename: str, fnNameBase: str, loopsFile: str, cvcPath: str) -> None:
    basename = os.path.splitext(os.path.basename(filename))[0]

    # begin state transition
    wrapBeforeState: Any = None
    wrapAfterState: Any = None
    wrapTransitionArgs: Any = None
    nextVc: Any = None

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
            finalState_0 = Var(
                fnNameBase + "_next_state" + "_0_cmd1_" + wrapAfterState.name,
                parseTypeRef(wrapAfterState.type),
            )
            finalState_1 = Var(
                fnNameBase + "_next_state" + "_1_cmd1_" + wrapAfterState.name,
                parseTypeRef(wrapAfterState.type),
            )
            nextVc = Eq(finalState_0, finalState_1)

        return (
            Implies(Eq(prevAfterState, beforeState), nextVc)
            if prevAfterState
            else nextVc,
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsStateTransition_0_cmd0,
        _,
        predsStateTransition_0_cmd0,
        nextVc,
        _,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_0_cmd0",
    )

    beforeState_0_cmd0 = Var(
        fnNameBase + "_next_state" + "_0_cmd0_" + wrapBeforeState.name,
        parseTypeRef(wrapBeforeState.type),
    )
    wrapAfterState = Var(
        fnNameBase + "_next_state" + "_0_cmd0_" + wrapAfterState.name,
        parseTypeRef(wrapAfterState.type),
    )
    afterState_0_cmd0 = wrapAfterState
    transitionArgs_0_cmd0 = [
        Var(fnNameBase + "_next_state" + "_0_cmd0_" + v.name, parseTypeRef(v.type))
        for v in wrapTransitionArgs
    ]

    (
        vcVarsStateTransition_0_cmd1,
        _,
        predsStateTransition_0_cmd1,
        nextVc,
        _,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_0_cmd1",
    )

    beforeState_0_cmd1 = Var(
        fnNameBase + "_next_state" + "_0_cmd1_" + wrapBeforeState.name,
        parseTypeRef(wrapBeforeState.type),
    )
    wrapAfterState = Var(
        fnNameBase + "_next_state" + "_0_cmd1_" + wrapAfterState.name,
        parseTypeRef(wrapAfterState.type),
    )
    afterState_0_cmd1 = wrapAfterState
    transitionArgs_0_cmd1 = [
        Var(fnNameBase + "_next_state" + "_0_cmd1_" + v.name, parseTypeRef(v.type))
        for v in wrapTransitionArgs
    ]

    wrapAfterState = None

    (
        vcVarsStateTransition_1_cmd0,
        _,
        predsStateTransition_1_cmd0,
        nextVc,
        _,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_1_cmd0",
    )

    beforeState_1_cmd0 = Var(
        fnNameBase + "_next_state" + "_1_cmd0_" + wrapBeforeState.name,
        parseTypeRef(wrapBeforeState.type),
    )
    wrapAfterState = Var(
        fnNameBase + "_next_state" + "_1_cmd0_" + wrapAfterState.name,
        parseTypeRef(wrapAfterState.type),
    )
    afterState_1_cmd0 = wrapAfterState
    transitionArgs_1_cmd0 = [
        Var(fnNameBase + "_next_state" + "_1_cmd0_" + v.name, parseTypeRef(v.type))
        for v in wrapTransitionArgs
    ]

    (
        vcVarsStateTransition_1_cmd1,
        _,
        predsStateTransition_1_cmd1,
        nextVc,
        _,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransition,
        fnNameSuffix="_1_cmd1",
    )

    beforeState_1_cmd1 = Var(
        fnNameBase + "_next_state" + "_1_cmd1_" + wrapBeforeState.name,
        parseTypeRef(wrapBeforeState.type),
    )
    wrapAfterState = Var(
        fnNameBase + "_next_state" + "_1_cmd1_" + wrapAfterState.name,
        parseTypeRef(wrapAfterState.type),
    )
    afterState_1_cmd1 = wrapAfterState
    transitionArgs_1_cmd1 = [
        Var(fnNameBase + "_next_state" + "_1_cmd1_" + v.name, parseTypeRef(v.type))
        for v in wrapTransitionArgs
    ]

    combinedVCVars = (
        vcVarsStateTransition_0_cmd0.union(vcVarsStateTransition_0_cmd1)
        .union(vcVarsStateTransition_1_cmd0)
        .union(vcVarsStateTransition_1_cmd1)
    )

    combinedPreds = (
        predsStateTransition_0_cmd0
        + predsStateTransition_0_cmd1
        + predsStateTransition_1_cmd0
        + predsStateTransition_1_cmd1
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
            ),
        ),
        nextVc,
    )
    # end state transition

    toSMT(
        [],
        combinedVCVars,
        [],
        combinedPreds,
        combinedVC,
        "./synthesisLogs/aci-test.smt",
        [],
        [],
    )

    procVerify = subprocess.run(
        [
            cvcPath,
            "--lang=smt",
            "--produce-models",
            "--tlimit=100000",
            "./synthesisLogs/aci-test.smt",
        ],
        stdout=subprocess.PIPE,
    )

    procOutput = procVerify.stdout
    resultVerify = procOutput.decode("utf-8").split("\n")

    def lookup_var(v: Expr) -> Expr:
        for line in resultVerify:
            if line.startswith("(define-fun " + v.args[0] + " "):
                return toExpr(generateAST(line)[0][4], [], [], {}, {})
        raise Exception("Could not find variable " + v.args[0])

    if resultVerify[0] == "sat" or resultVerify[0] == "unknown":
        print("Counterexample Found")
        print(f"Command 1: {[lookup_var(v) for v in transitionArgs_0_cmd0]}")
        print(f"Command 2: {[lookup_var(v) for v in transitionArgs_0_cmd1]}")
        print(f"Initial State: {lookup_var(beforeState_0_cmd0)}")
        print()
        print(f"After Command 1:")
        print(f"Actor 1: {lookup_var(afterState_0_cmd0)}")
        print(f"Actor 2: {lookup_var(afterState_1_cmd0)}")
        print()
        print(f"After Command 2:")
        print(f"Actor 1: {lookup_var(afterState_0_cmd1)}")
        print(f"Actor 2: {lookup_var(afterState_1_cmd1)}")
    else:
        print("Actor is commutative")


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

    # begin state transition
    extraVarsStateTransition = set()
    stateTypeOrig: Type = None  # type: ignore
    beforeStateOrigLink: Expr = None  # type: ignore
    beforeStateForPSLink: Expr = None  # type: ignore
    secondStateTransitionArgs: List[Expr] = None  # type: ignore

    def summaryWrapStateTransition(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        nonlocal stateTypeOrig
        nonlocal beforeStateOrigLink
        nonlocal beforeStateForPSLink
        nonlocal secondStateTransitionArgs

        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

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

        beforeStateForPS = Var(beforeStateOrig.name + "_for_ps", synthStateType)
        extraVarsStateTransition.add(beforeStateForPS)
        beforeStateForPSLink = beforeStateForPS

        afterStateForPS = Var(afterStateOrig.name + "_for_ps", synthStateType)
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
                    observeEquivalence(beforeStateOrig, beforeStateForPS),
                    ps,  # type: ignore
                ),
                And(
                    supportedCommand(beforeStateForPS, origArgs[1:]),
                    observeEquivalence(afterStateOrig, afterStateForPS),
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

    extraVarsPriorStateTransition = set()

    def summaryWrapPriorStateTransition(
        ps: MLInst,
    ) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        beforeStateOrig = typing.cast(ValueRef, origArgs[0])
        afterStateOrig = typing.cast(ValueRef, origReturn)

        beforeStateForPS = Var(beforeStateOrig.name + "_for_ps_prior", synthStateType)
        extraVarsPriorStateTransition.add(beforeStateForPS)

        afterStateForPS = Var(afterStateOrig.name + "_for_ps_prior", synthStateType)
        extraVarsPriorStateTransition.add(afterStateForPS)

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
                    inOrder(origArgs[1:], secondStateTransitionArgs),
                    ps,  # type: ignore
                ),
                vcStateTransition,
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsPriorStateTransition,
        _,
        predsPriorStateTransition,
        vcStateTransition,
        _,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapPriorStateTransition,
        fnNameSuffix="_prior_state",
    )

    vcVarsPriorStateTransition = vcVarsPriorStateTransition.union(
        extraVarsPriorStateTransition
    )
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

    synthInitState = Var("synth_init_state", synthStateType)

    origInitState: Expr = None  # type: ignore

    extraVarsInitState.add(synthInitState)

    def summaryWrapStateTransitionForInitStateCheck(
        ps: MLInst,
    ) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        beforeState = typing.cast(ValueRef, origArgs[0])
        nonlocal origInitState
        origInitState = Var("orig_init_state", parseTypeRef(beforeState.type))
        extraVarsInitState.add(origInitState)
        afterState = typing.cast(ValueRef, origReturn)

        afterStateForPS = Var(
            afterState.name + "_for_init_state_transition", synthStateType
        )
        extraVarsInitState.add(afterStateForPS)

        newReturn = afterStateForPS

        newArgs = list(origArgs)
        newArgs[0] = synthInitState

        ps.operands = tuple(list(ps.operands[:2]) + [newReturn] + newArgs)

        return (
            And(
                supportedCommand(synthInitState, origArgs[1:]),
                Implies(
                    And(
                        Eq(origInitState, beforeState),
                        ps,  # type: ignore
                    ),
                    observeEquivalence(afterState, afterStateForPS),
                ),
            ),
            list(ps.operands[2:]),  # type: ignore
        )

    (
        vcVarsInitStateTransition,
        _,
        predsInitStateTransition,
        initStateTransitionVc,
        _,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapStateTransitionForInitStateCheck,
        fnNameSuffix="_init_state",
    )

    def summaryWrapInitState(ps: MLInst) -> typing.Tuple[Expr, typing.List[Expr]]:
        origReturn = ps.operands[2]

        returnedInitState = typing.cast(ValueRef, origReturn)

        return (
            Implies(
                And(
                    Eq(synthInitState, initState()),
                    Eq(returnedInitState, origInitState),
                ),
                And(
                    observeEquivalence(returnedInitState, synthInitState),
                    initStateTransitionVc,
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
        Var(f"supported_arg_{i}", secondStateTransitionArgs[i].type)  # type: ignore
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
        vcVarsStateTransition.union(vcVarsPriorStateTransition)
        .union(vcVarsQuery)
        .union(vcVarsInitStateTransition)
        .union(vcVarsInitState)
    )

    combinedInvAndPs = (
        invAndPsStateTransition
        + invAndPsQuery
        + invAndPsInitState
        + invAndPsEquivalence
        + invAndPsSupported
    )

    combinedPreds = (
        predsStateTransition
        + predsPriorStateTransition
        + predsQuery
        + predsInitStateTransition
        + predsInitState
    )

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransition
        + loopAndPsInfoQuery
        + loopAndPsInfoInitState
        + invAndPsEquivalence  # type: ignore
        + invAndPsSupported  # type: ignore
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
        unboundedInts=unboundedInts,
    )

import os

from analysis import CodeInfo, analyze
from ir import *

from llvmlite.binding import ValueRef

import typing
from typing import Callable, Union, Protocol

from synthesis_common import SynthesisFailed, VerificationFailed


def observeEquivalence(inputState: Expr, synthState: Expr) -> Expr:
    return Call("equivalence", Bool(), inputState, synthState)


def opsListInvariant(
    fnNameBase: str, synthState: Expr, synthStateType: Type, opType: Type
) -> Expr:
    return And(
        Eq(
            Call(
                "apply_state_transitions",
                synthStateType,
                TupleGet(synthState, IntLit(len(synthStateType.args) - 1)),
                Var(
                    f"{fnNameBase}_next_state",
                    Fn(synthStateType, synthStateType, *opType.args),
                ),
            ),
            synthState,
        ),
        Call(
            "ops_in_order",
            Bool(),
            TupleGet(synthState, IntLit(len(synthStateType.args) - 1)),
        ),
    )


def supportedCommand(synthState: Expr, args: typing.Any) -> Expr:
    return Call("supportedCommand", Bool(), synthState, *args)


def unpackOp(op: Expr) -> typing.List[Expr]:
    if op.type.name == "Tuple":
        return [TupleGet(op, IntLit(i)) for i in range(len(op.type.args))]
    else:
        return [op]


def opListAdditionalFns(
    synthStateType: Type,
    opType: Type,
    initState: Callable[[], Expr],
    inOrder: Callable[[typing.Any, typing.Any], Expr],
    opPrecondition: Callable[[typing.Any], Expr],
) -> typing.List[Expr]:
    def list_length(l: Expr) -> Expr:
        return Call("list_length", Int(), l)

    def list_get(l: Expr, i: Expr) -> Expr:
        return Call("list_get", opType, l, i)

    def list_tail(l: Expr, i: Expr) -> Expr:
        return Call("list_tail", List(opType), l, i)

    data = Var("data", List(opType))
    next_state_fn = Var(
        "next_state_fn",
        Fn(
            synthStateType,
            synthStateType,
            *(opType.args if opType.name == "Tuple" else [opType]),
        ),
    )

    reduce_fn = FnDecl(
        "apply_state_transitions",
        synthStateType,
        Ite(
            Eq(list_length(data), IntLit(0)),
            MakeTuple(*initState().args, Call("list_empty", List(opType))),
            CallValue(
                next_state_fn,
                Call(
                    "apply_state_transitions",
                    synthStateType,
                    list_tail(data, IntLit(1)),
                    next_state_fn,
                ),
                *(
                    [
                        TupleGet(list_get(data, IntLit(0)), IntLit(i))
                        for i in range(len(opType.args))
                    ]
                    if opType.name == "Tuple"
                    else [list_get(data, IntLit(0))]
                ),
            ),
        ),
        data,
        next_state_fn,
    )

    next_op = Var("next_op", opType)
    ops_in_order_helper = FnDecl(
        "ops_in_order_helper",
        Bool(),
        And(
            opPrecondition(unpackOp(next_op)),
            Ite(
                Eq(list_length(data), IntLit(0)),
                BoolLit(True),
                And(
                    inOrder(unpackOp(list_get(data, IntLit(0))), unpackOp(next_op)),
                    Call(
                        "ops_in_order_helper",
                        Bool(),
                        list_get(data, IntLit(0)),
                        list_tail(data, IntLit(1)),
                    ),
                ),
            ),
        ),
        next_op,
        data,
    )

    ops_in_order = FnDecl(
        "ops_in_order",
        Bool(),
        Ite(
            Eq(list_length(data), IntLit(0)),
            BoolLit(True),
            Call(
                "ops_in_order_helper",
                Bool(),
                list_get(data, IntLit(0)),
                list_tail(data, IntLit(1)),
            ),
        ),
        data,
    )

    return [reduce_fn, ops_in_order_helper, ops_in_order]


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
        uid: int = 0,
        noVerify: bool = False,
        unboundedInts: bool = False,
        listBound: int = 1,
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
    opPrecondition: Callable[[typing.Any], Expr],
    grammar: Callable[[CodeInfo], Expr],
    grammarQuery: Callable[[CodeInfo], Expr],
    grammarEquivalence: Callable[[Expr, Expr], Expr],
    targetLang: Callable[[], typing.List[Expr]],
    synthesize: SynthesizeFun,
    uid: int = 0,
    unboundedInts: bool = False,
    useOpList: bool = False,
    listBound: int = 1,
    log: bool = True,
) -> typing.List[Expr]:
    basename = os.path.splitext(os.path.basename(filename))[0]
    origSynthStateType = synthStateType

    opType: Type = None  # type: ignore

    def supportedCommandWithList(synthState: Expr, args: typing.Any) -> Expr:
        return And(
            opPrecondition(args),
            Ite(
                Eq(
                    Call(
                        "list_length",
                        Int(),
                        TupleGet(synthState, IntLit(len(synthStateType.args) - 1)),
                    ),
                    IntLit(0),
                ),
                BoolLit(True),
                inOrder(
                    unpackOp(
                        Call(
                            "list_get",
                            opType,
                            TupleGet(synthState, IntLit(len(synthStateType.args) - 1)),
                            IntLit(0),
                        )
                    ),
                    args,
                ),
            ),
        )

    # begin state transition (in order)
    stateTypeOrig: Type = None  # type: ignore
    secondStateTransitionArgs: typing.List[Expr] = []
    op_arg_types: typing.List[Type] = []

    extraVarsPriorStateTransitionInOrder = set()

    def summaryWrapPriorStateTransition(
        ps: MLInst,
    ) -> typing.Tuple[Expr, typing.List[Expr]]:
        nonlocal stateTypeOrig
        nonlocal secondStateTransitionArgs
        nonlocal op_arg_types
        nonlocal opType
        nonlocal synthStateType

        origReturn = ps.operands[2]
        origArgs = ps.operands[3:]

        for i in range(len(origArgs) - 1):
            op_arg_types.append(parseTypeRef(origArgs[i + 1].type))  # type: ignore
        opType = Tuple(*op_arg_types) if len(op_arg_types) > 1 else op_arg_types[0]
        if useOpList:
            synthStateType = Tuple(*synthStateType.args, List(opType))

        secondStateTransitionArgs = [
            Var(f"second_transition_arg_{i}", parseTypeRef(origArgs[i + 1].type))  # type: ignore
            for i in range(len(origArgs) - 1)
        ]
        for arg in secondStateTransitionArgs:
            extraVarsPriorStateTransitionInOrder.add(arg)

        beforeStateOrig = typing.cast(ValueRef, origArgs[0])
        afterStateOrig = typing.cast(ValueRef, origReturn)

        stateTypeOrig = parseTypeRef(beforeStateOrig.type)

        beforeStateForPS = Var(beforeStateOrig.name + "_for_ps_prior", synthStateType)
        extraVarsPriorStateTransitionInOrder.add(beforeStateForPS)

        afterStateForPS = Var(afterStateOrig.name + "_for_ps_prior", synthStateType)
        extraVarsPriorStateTransitionInOrder.add(afterStateForPS)

        newReturn = afterStateForPS

        newArgs = list(origArgs)
        newArgs[0] = beforeStateForPS

        return (
            Implies(
                And(
                    observeEquivalence(beforeStateOrig, beforeStateForPS),
                    *(
                        [
                            opsListInvariant(
                                fnNameBase, beforeStateForPS, synthStateType, opType
                            ),
                            supportedCommandWithList(beforeStateForPS, origArgs[1:]),
                        ]
                        if useOpList
                        else [
                            supportedCommand(beforeStateForPS, origArgs[1:]),
                        ]
                    ),
                    Eq(newReturn, Call(f"{fnNameBase}_next_state", newReturn.type, *newArgs)),  # type: ignore
                ),
                And(
                    observeEquivalence(afterStateOrig, afterStateForPS),
                    *(
                        [
                            Implies(
                                inOrder(origArgs[1:], secondStateTransitionArgs),
                                supportedCommand(
                                    afterStateForPS, secondStateTransitionArgs
                                ),
                            )
                        ]
                        if not useOpList
                        else []
                    ),
                ),
            ),
            [newReturn] + newArgs,  # type: ignore
        )

    (
        vcVarsPriorStateTransitionInOrder,
        invAndPsStateTransition,
        predsPriorStateTransitionInOrder,
        vcStateTransitionInOrder,
        loopAndPsInfoStateTransition,
    ) = analyze(
        filename,
        fnNameBase + "_next_state",
        loopsFile,
        wrapSummaryCheck=summaryWrapPriorStateTransition,
        fnNameSuffix="_prior_state",
        log=log,
    )

    vcVarsPriorStateTransition = vcVarsPriorStateTransitionInOrder.union(
        extraVarsPriorStateTransitionInOrder
    )

    loopAndPsInfoStateTransition[0].retT = (
        loopAndPsInfoStateTransition[0].modifiedVars[0].type
    )
    loopAndPsInfoStateTransition[0].modifiedVars = []

    stateTransitionSynthNode = grammar(loopAndPsInfoStateTransition[0])

    invAndPsStateTransition = (
        [
            Synth(
                stateTransitionSynthNode.args[0],
                MakeTuple(
                    *stateTransitionSynthNode.args[1].args,
                    Call(
                        "list_prepend",
                        List(opType),
                        MakeTuple(*loopAndPsInfoStateTransition[0].readVars[1:])
                        if len(loopAndPsInfoStateTransition[0].readVars[1:]) > 1
                        else loopAndPsInfoStateTransition[0].readVars[1],
                        TupleGet(
                            loopAndPsInfoStateTransition[0].readVars[0],
                            IntLit(len(synthStateType.args) - 1),
                        ),
                    ),
                ),
                *stateTransitionSynthNode.args[2:],
            )
        ]
        if useOpList
        else [stateTransitionSynthNode]
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

        return (
            Implies(
                observeEquivalence(beforeState, beforeStateForQuery),
                Eq(origReturn, Call(f"{fnNameBase}_response", origReturn.type, *newArgs)),  # type: ignore
            ),
            [origReturn] + newArgs,
        )

    (vcVarsQuery, invAndPsQuery, predsQuery, vcQuery, loopAndPsInfoQuery) = analyze(
        filename,
        fnNameBase + "_response",
        loopsFile,
        wrapSummaryCheck=summaryWrapQuery,
        log=log,
    )

    vcVarsQuery = vcVarsQuery.union(extraVarsQuery)
    loopAndPsInfoQuery[0].retT = loopAndPsInfoQuery[0].modifiedVars[0].type
    loopAndPsInfoQuery[0].modifiedVars = []
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
                    Eq(
                        synthInitState,
                        MakeTuple(*initState().args, Call("list_empty", List(opType)))
                        if useOpList
                        else initState(),
                    ),
                ),
                And(
                    observeEquivalence(returnedInitState, synthInitState),
                    opsListInvariant(fnNameBase, synthInitState, synthStateType, opType)
                    if useOpList
                    else Implies(
                        opPrecondition(init_op_arg_vars),
                        supportedCommand(synthInitState, init_op_arg_vars),
                    ),
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
        log=log,
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
                *(
                    [grammarStateInvariant(synthStateForEquivalence)]
                    if not useOpList
                    else []
                ),
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
    invAndPsSupported = (
        [
            Synth(
                "supportedCommand",
                grammarSupportedCommand(synthStateForSupported, argList),
                synthStateForSupported,
                *argList,
            )
        ]
        if not useOpList
        else []
    )
    # end equivalence

    if log:
        print("====== synthesis")

    combinedVCVars = vcVarsPriorStateTransition.union(vcVarsQuery).union(
        vcVarsInitState
    )

    combinedInvAndPs = (
        invAndPsStateTransition
        + invAndPsQuery
        + invAndPsInitState
        + invAndPsEquivalence
        + invAndPsSupported
    )

    combinedPreds = predsPriorStateTransitionInOrder + predsQuery + predsInitState

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransition
        + loopAndPsInfoQuery
        + loopAndPsInfoInitState
        + invAndPsEquivalence  # type: ignore
        + invAndPsSupported  # type: ignore
    )
    combinedVC = And(vcStateTransitionInOrder, vcQuery, vcInitState)

    lang = targetLang()
    if useOpList:
        lang = lang + opListAdditionalFns(
            synthStateType, opType, initState, inOrder, opPrecondition
        )

    try:
        out = synthesize(
            basename,
            lang,
            combinedVCVars,
            combinedInvAndPs,
            combinedPreds,
            combinedVC,
            combinedLoopAndPsInfo,
            cvcPath,
            uid=uid,
            unboundedInts=unboundedInts,
            noVerify=useOpList,
            listBound=listBound,
        )
    except VerificationFailed:
        print("INCREASING LIST BOUND TO", listBound + 1)
        return synthesize_actor(
            filename,
            fnNameBase,
            loopsFile,
            cvcPath,
            origSynthStateType,
            initState,
            grammarStateInvariant,
            grammarSupportedCommand,
            inOrder,
            opPrecondition,
            grammar,
            grammarQuery,
            grammarEquivalence,
            targetLang,
            synthesize,
            uid,
            unboundedInts,
            useOpList,
            listBound=listBound + 1,
            log=log,
        )

    if useOpList:
        print(f"Re-synthesizing to identify invariants (list bound: {listBound})")
        equivalence_fn = [x for x in out if x.args[0] == "equivalence"][0]
        state_transition_fn = [
            x for x in out if x.args[0] == f"{fnNameBase}_next_state"
        ][0]
        query_fn = [x for x in out if x.args[0] == f"{fnNameBase}_response"][0]

        equivalence_fn.args[3] = Var(
            equivalence_fn.args[3].args[0],
            Tuple(*equivalence_fn.args[3].type.args[:-1]),
        )

        equivalence_fn.args[1] = equivalence_fn.args[1].rewrite(
            {equivalence_fn.args[3].args[0]: equivalence_fn.args[3]}
        )

        state_transition_fn.args[2] = Var(
            state_transition_fn.args[2].args[0],
            Tuple(*state_transition_fn.args[2].type.args[:-1]),
        )

        state_transition_fn.args[1] = MakeTuple(
            *[
                e.rewrite(
                    {state_transition_fn.args[2].args[0]: state_transition_fn.args[2]}
                )
                for e in state_transition_fn.args[1].args[:-1]
            ]
        )

        query_fn.args[2] = Var(
            query_fn.args[2].args[0], Tuple(*query_fn.args[2].type.args[:-1])
        )

        query_fn.args[1] = query_fn.args[1].rewrite(
            {query_fn.args[2].args[0]: query_fn.args[2]}
        )

        try:
            return synthesize_actor(
                filename,
                fnNameBase,
                loopsFile,
                cvcPath,
                origSynthStateType,
                initState,
                grammarStateInvariant,
                grammarSupportedCommand,
                inOrder,
                opPrecondition,
                lambda _: Synth(
                    state_transition_fn.args[0],
                    state_transition_fn.args[1],
                    *state_transition_fn.args[2:],
                ),
                lambda _: Synth(query_fn.args[0], query_fn.args[1], *query_fn.args[2:]),
                lambda a, b: equivalence_fn.args[1],  # type: ignore
                targetLang,
                synthesize,
                uid,
                unboundedInts,
                useOpList=False,
                listBound=listBound,
                log=log,
            )
        except SynthesisFailed:
            print("INCREASING LIST BOUND TO", listBound + 1)
            return synthesize_actor(
                filename,
                fnNameBase,
                loopsFile,
                cvcPath,
                origSynthStateType,
                initState,
                grammarStateInvariant,
                grammarSupportedCommand,
                inOrder,
                opPrecondition,
                grammar,
                grammarQuery,
                grammarEquivalence,
                targetLang,
                synthesize,
                uid,
                unboundedInts,
                useOpList,
                listBound=listBound + 1,
                log=log,
            )
    else:
        return out

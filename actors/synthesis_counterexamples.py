import subprocess
import os

from analysis import CodeInfo, analyze
from ir import *

from llvmlite.binding import ValueRef

import typing
from typing import Callable, Union, Protocol, IO

from synthesis_common import SynthesisFailed, VerificationFailed, verify_synth_result, generateTypes
from synthesize_cvc5 import toExpr
from synthesize_rosette import parseOutput, generateAST


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
                Var(
                    f"{fnNameBase}_init_state",
                    Fn(synthStateType),
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

    init_state_fn = Var("init_state_fn", Fn(synthStateType))

    reduce_fn = FnDecl(
        "apply_state_transitions",
        synthStateType,
        Ite(
            Eq(list_length(data), IntLit(0)),
            CallValue(init_state_fn),
            CallValue(
                next_state_fn,
                Call(
                    "apply_state_transitions",
                    synthStateType,
                    list_tail(data, IntLit(1)),
                    next_state_fn,
                    init_state_fn,
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
        init_state_fn,
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
    stateTypeHint: typing.Optional[Type] = None,
    opArgTypeHint: typing.Optional[typing.List[Type]] = None,
    queryArgTypeHint: typing.Optional[typing.List[Type]] = None,
    queryRetTypeHint: typing.Optional[Type] = None,
    uid: int = 0,
    unboundedInts: bool = False,
    useOpList: bool = False,
    listBound: int = 1,
    log: bool = True,
    skipSynth: bool = False,
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
    stateTransitionArgs: typing.List[Expr] = []
    op_arg_types: typing.List[Type] = []

    extraVarsStateTransition = set()

    def summaryWrapStateTransition(
        ps: MLInst,
    ) -> typing.Tuple[Expr, typing.List[Expr]]:
        nonlocal stateTypeOrig
        nonlocal stateTransitionArgs
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

        stateTransitionArgs = [
            Var(f"state_transition_arg_{i}", parseTypeRef(origArgs[i + 1].type))  # type: ignore
            for i in range(len(origArgs) - 1)
        ]
        for arg in stateTransitionArgs:
            extraVarsStateTransition.add(arg)

        beforeStateOrig = typing.cast(ValueRef, origArgs[0])
        afterStateOrig = typing.cast(ValueRef, origReturn)

        stateTypeOrig = parseTypeRef(beforeStateOrig.type)

        beforeStateForPS = Var(
            beforeStateOrig.name + "_for_state_transition", synthStateType
        )
        extraVarsStateTransition.add(beforeStateForPS)

        afterStateForPS = Var(
            afterStateOrig.name + "_for_state_transition", synthStateType
        )
        extraVarsStateTransition.add(afterStateForPS)

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
                                inOrder(origArgs[1:], stateTransitionArgs),
                                supportedCommand(afterStateForPS, stateTransitionArgs),
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
        fnNameSuffix="_state_transition",
        log=log,
    )

    vcVarsStateTransition = vcVarsStateTransition.union(extraVarsStateTransition)

    if opArgTypeHint:
        for i in range(len(opArgTypeHint)):
            loopAndPsInfoStateTransition[0].readVars[i + 1].my_type = opArgTypeHint[i]  # type: ignore

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

    if queryArgTypeHint:
        for i in range(len(queryArgTypeHint) - 1):
            loopAndPsInfoQuery[0].readVars[i + 1].my_type = queryArgTypeHint[i]  # type: ignore

    loopAndPsInfoQuery[0].retT = (
        loopAndPsInfoQuery[0].modifiedVars[0].type  # type: ignore
        if queryRetTypeHint == None
        else queryRetTypeHint
    )
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
                        Call(f"{fnNameBase}_init_state", synthStateType),
                    )
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
    loopAndPsInfoInitState[0].retT = loopAndPsInfoInitState[0].modifiedVars[0].type
    loopAndPsInfoInitState[0].modifiedVars = []
    initStateSynthNode = initState()
    invAndPsInitState = [
        Synth(
            fnNameBase + "_init_state",
            MakeTuple(
                *initStateSynthNode.args,
                Call("list_empty", List(opType)),
            )
            if useOpList
            else MakeTuple(
                *initStateSynthNode.args,
            ),
        )
    ]
    # end init state

    # begin equivalence
    inputStateForEquivalence = Var(
        "inputState", stateTypeOrig if stateTypeHint == None else stateTypeHint  # type: ignore
    )
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
        Var(
            f"supported_arg_{i}",
            stateTransitionArgs[i].type
            if (opArgTypeHint == None)
            else opArgTypeHint[i],  # type: ignore
        )
        for i in range(len(stateTransitionArgs))
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

    combinedVCVars = vcVarsStateTransition.union(vcVarsQuery).union(vcVarsInitState)

    combinedInvAndPs = (
        invAndPsStateTransition
        + invAndPsQuery
        + invAndPsInitState
        + invAndPsEquivalence
        + invAndPsSupported
    )

    combinedPreds = predsStateTransition + predsQuery + predsInitState

    combinedLoopAndPsInfo: typing.List[Union[CodeInfo, Expr]] = (
        loopAndPsInfoStateTransition
        + loopAndPsInfoQuery
        + loopAndPsInfoInitState
        + invAndPsEquivalence  # type: ignore
        + invAndPsSupported  # type: ignore
    )
    combinedVC = And(vcStateTransition, vcQuery, vcInitState)

    lang = targetLang()
    if useOpList:
        lang = lang + opListAdditionalFns(
            synthStateType, opType, initState, inOrder, opPrecondition
        )

    if skipSynth:
        return  # type: ignore

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

    arg_for_state_transition = Var("arg_for_state_transition", Tuple(Set(Int()), Int()))
    arg1 = Var("arg1", Int())
    arg2 = Var("arg2", Int())
    broken_test_next_state = FnDecl(
        "test_next_state",
        Tuple(Set(Int()), Int()),
        MakeTuple(
            Call(
                "set-minus",
                Set(Int()),
                TupleGet(
                    arg_for_state_transition,
                    IntLit(0)
                ),
                Ite(
                    (Eq(arg1, IntLit(1))),
                    Call(
                        "set-singleton",
                        Set(Int()),
                        arg2
                    ),
                    Call(
                        "set-minus",
                        Set(Int()),
                        Call(
                            "set-create",
                            Set(Int())
                        ),
                        Call(
                            "set-create",
                            Set(Int())
                        )
                    )
                )
            ),
            IntLit(0)
        ),
        arg_for_state_transition,
        arg1,
        arg2
    )

    arg_for_query = Var("arg_for_query", Tuple(Set(Int()), Int()))
    arg1 = Var("arg1", Int())
    correct_test_response = FnDecl(
        "test_response",
        Int(),
        Ite(
            Call(
                "set-member",
                Bool(),
                arg1,
                Call(
                    "set-minus",
                    Set(Int()),
                    TupleGet(
                        arg_for_query,
                        IntLit(0)
                    ),
                    Call(
                        "set-create",
                        Set(Int())
                    )
                )
            ),
            IntLit(1),
            IntLit(0)
        ),
        arg_for_query,
        arg1
    )

    correct_test_init_state = FnDecl(
        "test_init_state",
        Tuple(Set(Int()), Int()),
        MakeTuple(
            Call(
                "set-create",
                Set(Int())
            ),
            IntLit(0)
        )
    )

    inputState = Var("inputState", Set(Int()))
    synthState = Var("synthState", Tuple(Set(Int()), Int()))
    correct_equivalence = FnDecl(
        "equivalence",
        Bool(),
        And(
            And(
                Eq(
                    Call(
                        "set-union",
                        Set(Int()),
                        Call (
                            "set-create",
                            Set(Int())
                        ),
                        inputState
                    ),
                    TupleGet(
                        synthState,
                        IntLit(0)
                    )
                )
            ),
            Or(
                BoolLit(True),
                BoolLit(True)
            )
        ),
        inputState,
        synthState
    )

    supported_synthState = Var("supported_synthState", Tuple(Set(Int()), Int()))
    supported_arg_0 = Var("supported_arg_0", Int())
    supported_arg_1 = Var("supported_arg_1", Int())
    correct_supportedCommand = FnDecl(
        "supportedCommand",
        Bool(),
        Ite(
            Eq(
                supported_arg_0,
                IntLit(1)
            ),
            Eq(
                supported_arg_1,
                supported_arg_1
            ),
            Eq(
                Call(
                    "set-create",
                    Set(Int())
                ),
                TupleGet(
                    supported_synthState,
                    IntLit(0)
                )
            )
        ),
        supported_synthState,
        supported_arg_0,
        supported_arg_1
    )

    print("\nbroken_test_next_state\n", broken_test_next_state)
    print("\ncorrect_test_response\n", correct_test_response)
    print("\ncorrect_test_init_state\n", correct_test_init_state)
    print("\ncorrect_equivalence\n", correct_equivalence)
    print("\ncorrect_supportedCommand\n", correct_supportedCommand)

    synthDir = "./synthesisLogs/"
    candidatesSMT = [broken_test_next_state, correct_test_response, correct_test_init_state, correct_equivalence, correct_supportedCommand]
    candidateDict = {
        'test_next_state': "(Tuple:(Tuple (Set Int) Int) (set-minus:(Set Int) (TupleGet:(Set Int) arg_for_state_transition (Lit:Int 0)) (Ite:(Set Int) (Eq:Bool arg1 (Lit:Int 1)) (set-singleton:(Set Int) arg2) (set-minus:(Set Int) (set-create:(Set Int) ) (set-create:(Set Int) )))) (Lit:Int 0))",
        'test_response': "(Ite:Int (set-member:Bool arg1 (set-minus:(Set Int) (TupleGet:(Set Int) arg_for_query (Lit:Int 0)) (set-create:(Set Int) )))(Lit:Int 1) (Lit:Int 0))",
        'test_init_state': "(Tuple:(Tuple (Set Int) Int) (set-create:(Set Int) ) (Lit:Int 0))",
        'equivalence': "(And:Bool (And:Bool (Eq:Bool (set-union:(Set Int) (set-create:(Set Int) ) inputState) (TupleGet:(Set Int) synthState (Lit:Int 0)))) (Or:Bool (Lit:Bool True) (Lit:Bool True)))",
        'supportedCommand': "(Ite:Bool (Eq:Bool supported_arg_0 (Lit:Int 1)) (Eq:Bool supported_arg_1 supported_arg_1) (Eq:Bool (set-create:(Set Int) ) (TupleGet:(Set Int) supported_synthState (Lit:Int 0))))"
    }
    fnsType = generateTypes(lang)   
    for synthFun in combinedInvAndPs:
        allVars = synthFun.args[2:]
        ceName = synthFun.args[0]
        fnsType[ceName] = Fn(
            synthFun.args[1].type,
            *[v.type for v in allVars]
        )

    try:
        # out = synthesize(
        #     basename,
        #     lang,
        #     combinedVCVars,
        #     combinedInvAndPs,
        #     combinedPreds,
        #     combinedVC,
        #     combinedLoopAndPsInfo,
        #     cvcPath,
        #     uid=uid,
        #     unboundedInts=unboundedInts,
        #     noVerify=useOpList,
        #     listBound=listBound,
        # )
        # Directly plug in
        resultVerify, verifyLogs = verify_synth_result(
            basename,
            lang,
            combinedVCVars,
            combinedPreds,
            combinedVC,
            combinedLoopAndPsInfo,
            cvcPath,
            synthDir,
            candidatesSMT,
            candidateDict,
            fnsType,
            uid
        )

        print("\n\nResult Verify\n", resultVerify, "\n")
        print("\n\nVerify Logs\n", verifyLogs, "\n")

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
            stateTypeHint=stateTypeHint,
            opArgTypeHint=opArgTypeHint,
            queryArgTypeHint=queryArgTypeHint,
            queryRetTypeHint=queryRetTypeHint,
            uid=uid,
            unboundedInts=unboundedInts,
            useOpList=useOpList,
            listBound=listBound + 1,
            log=log,
        )

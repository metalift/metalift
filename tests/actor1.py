import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Or, Not, Gt, Ge, Eq, Le, Le, Sub, Synth, Call, Int, IntLit, Bool, BoolLit, FnDecl, Var, Add, Implies, Ite, Set, Tuple, TupleSel, MakeTuple

if False:
  from synthesize_rosette import synthesize
else:
  from synthesis import synthesize_new as synthesize

synthStateType = Tuple(Set(Int()), Set(Int()))

def observeEquivalence(inputState, synthState):
  return Call(
    "equivalence",
    Bool(),
    inputState,
    synthState
  )

def equivalenceGrammar():
  inputState = Var("inputState", Set(Int()))
  synthState = Var("synthState", synthStateType)

  equivalent = Eq(
    inputState,
    Call(
      "setminus", Set(Int()),
      TupleSel(synthState, 0),
      TupleSel(synthState, 1)
    )
  )

  return Synth("equivalence", equivalent, inputState, synthState)

def stateInvariant(synthState):
  # delete set is a subset of the insert set
  return Call("subset", Bool(), TupleSel(synthState, 1), TupleSel(synthState, 0))

def supportedCommand(synthState, args):
  add = args[0]
  value = args[1]

  return Ite(
    Eq(add, IntLit(1)),
    # insertion works if the elem is not in the deletion set
    # (which means it's in both sets)
    Not(Call("member", Bool(), value, TupleSel(synthState, 1))),
    # deletion can work even if not in the insertion set
    # because we can just add the element to both sets
    # which results in an observed-equivalent final state
    BoolLit(True)
  )

def grammarQuery(ci: CodeInfo):
  name = ci.name

  inputState = ci.readVars[0]
  outputVar = ci.modifiedVars[0]

  stateSet1 = TupleSel(inputState, 0)
  stateSet2 = TupleSel(inputState, 1)

  inputValue = ci.readVars[1]

  setIn = Choose(stateSet1, stateSet2)
  setContains = Call("member", Bool(), inputValue, setIn)

  setContainTransformed = Choose(
    setContains,
    Not(setContains)
  )

  setContainTransformed = Choose(
    setContainTransformed,
    And(setContainTransformed, setContainTransformed)
  )

  intLit = Choose(IntLit(0), IntLit(1))

  out = Ite(
    setContainTransformed,
    intLit,
    intLit
  )

  summary = Eq(
    outputVar,
    out
  )

  return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):
    raise Exception("no invariant")
  else:  # ps
    inputState = ci.readVars[0]
    stateSet1 = TupleSel(inputState, 0)
    stateSet2 = TupleSel(inputState, 1)

    inputAdd = ci.readVars[1]
    inputValue = ci.readVars[2]

    outputState = ci.modifiedVars[0]
        
    emptySet = Call("as emptyset (Set Int)", Set(Int()))

    intLit = Choose(IntLit(0), IntLit(1))

    condition = Eq(inputAdd, intLit)

    setIn = Choose(
      stateSet1, stateSet2,
      Call("singleton", Set(Int()), inputValue),
    )

    setTransform = Choose(
      setIn,
      Call("union", Set(Int()), setIn, setIn)
    )

    chosenTransform = Choose(
      setTransform,
      Ite(
        condition,
        setTransform,
        setTransform
      )
    )

    summary = Eq(outputState, MakeTuple(
      chosenTransform,
      chosenTransform
    ))

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def initState():
  return MakeTuple(
    Var("(as emptyset (Set Int))", Set(Int())),
    Var("(as emptyset (Set Int))", Set(Int()))
  )

def targetLang():
  return []

if __name__ == "__main__":
  filename = sys.argv[1]
  basename = os.path.splitext(os.path.basename(filename))[0]

  fnNameBase = sys.argv[2]
  loopsFile = sys.argv[3]
  cvcPath = sys.argv[4]

  # begin state transition
  extraVarsStateTransition = set()

  def summaryWrapStateTransition(ps):
    origReturn = ps.operands[2]
    origArgs = ps.operands[3:]

    beforeState = origArgs[0]
    afterState = origReturn

    beforeStateForPS = Var(beforeState.name + "_for_ps", synthStateType)
    extraVarsStateTransition.add(beforeStateForPS)

    afterStateForPS = Var(afterState.name + "_for_ps", synthStateType)
    extraVarsStateTransition.add(afterStateForPS)

    newReturn = afterStateForPS

    newArgs = list(origArgs)
    newArgs[0] = beforeStateForPS

    ps.operands = tuple(list(ps.operands[:2]) + [newReturn] + newArgs)
    
    return Implies(
      And(
        stateInvariant(beforeStateForPS),
        And(
          supportedCommand(beforeStateForPS, origArgs[1:]),
          observeEquivalence(beforeState, beforeStateForPS)
        )
      ),
      Implies(
        ps,
        And(
          stateInvariant(afterStateForPS),
          observeEquivalence(afterState, afterStateForPS)
        )
      )
    ), ps.operands[2:]

  (vcVarsStateTransition, invAndPsStateTransition, predsStateTransition, vcStateTransition, loopAndPsInfoStateTransition) = analyze(
    filename, fnNameBase + "_next_state", loopsFile,
    wrapSummaryCheck=summaryWrapStateTransition
  )

  vcVarsStateTransition = vcVarsStateTransition.union(extraVarsStateTransition)
  invAndPsStateTransition = [grammar(ci) for ci in loopAndPsInfoStateTransition]
  # end state transition

  # begin query
  extraVarsQuery = set()

  def summaryWrapQuery(ps):
    origReturn = ps.operands[2]
    origArgs = ps.operands[3:]

    beforeState = origArgs[0]

    beforeStateForQuery = Var(beforeState.name + "_for_query", synthStateType)
    extraVarsQuery.add(beforeStateForQuery)

    newArgs = list(origArgs)
    newArgs[0] = beforeStateForQuery

    ps.operands = tuple(list(ps.operands[:2]) + [origReturn] + newArgs)

    return Implies(
      And(
        stateInvariant(beforeStateForQuery),
        observeEquivalence(beforeState, beforeStateForQuery)
      ),
      ps
    ), ps.operands[2:]

  (vcVarsQuery, invAndPsQuery, predsQuery, vcQuery, loopAndPsInfoQuery) = analyze(
    filename, fnNameBase + "_response", loopsFile,
    wrapSummaryCheck=summaryWrapQuery
  )

  vcVarsQuery = vcVarsQuery.union(extraVarsQuery)
  invAndPsQuery = [grammarQuery(ci) for ci in loopAndPsInfoQuery]
  # end query

  # begin init state
  extraVarsInitstateInvariantVC = set()
  initStateVar = Var("initState", synthStateType)
  extraVarsInitstateInvariantVC.add(initStateVar)
  initstateInvariantVC = Implies(
    Eq(initStateVar, initState()),
    stateInvariant(initStateVar)
  )
  # end init state

  # begin equivalence
  invAndPsEquivalence = [equivalenceGrammar()]
  # end equivalence

  print("====== synthesis")
  
  combinedVCVars = vcVarsStateTransition.union(vcVarsQuery).union(extraVarsInitstateInvariantVC)

  combinedInvAndPs = invAndPsStateTransition + invAndPsQuery + invAndPsEquivalence

  combinedPreds = predsStateTransition + predsQuery

  combinedLoopAndPsInfo = loopAndPsInfoStateTransition + loopAndPsInfoQuery

  combinedVC = And(
    vcStateTransition,
    vcQuery,
    initstateInvariantVC
  )

  lang = targetLang()

  candidates = synthesize(
    basename, lang, combinedVCVars,
    combinedInvAndPs,
    combinedPreds, combinedVC, combinedLoopAndPsInfo, cvcPath
  )

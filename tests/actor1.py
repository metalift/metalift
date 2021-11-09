import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Or, Not, Gt, Ge, Eq, Le, Le, Sub, Synth, Call, Int, IntLit, Bool, BoolLit, FnDecl, Var, Add, Implies, Ite, Set, Tuple, TupleSel, MakeTuple

if False:
  from synthesize_rosette import synthesize
else:
  from synthesis import synthesize_new as synthesize

synthStateType = Tuple(Set(Int()), Set(Int()))

# todo: synthesize so that equivalence implies equal queries
def observeEquivalence(inputState, synthState):
  return Eq(
    inputState,
    Call(
      "setminus", Set(Int()),
      TupleSel(synthState, 0),
      TupleSel(synthState, 1)
    )
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

  print("====== synthesis")
  invAndPsStateTransition = [grammar(ci) for ci in loopAndPsInfoStateTransition]

  extraVarsInitstateInvariantVC = set()
  initStateVar = Var("initState", synthStateType)
  extraVarsInitstateInvariantVC.add(initStateVar)
  initstateInvariantVC = Implies(
    Eq(initStateVar, initState()),
    stateInvariant(initStateVar)
  )

  combinedVCVars = vcVarsStateTransition.union(extraVarsInitstateInvariantVC)

  combinedInvAndPs = invAndPsStateTransition

  combinedPreds = predsStateTransition

  combinedLoopAndPsInfo = loopAndPsInfoStateTransition

  combinedVC = And(
    initstateInvariantVC,
    vcStateTransition
  )

  lang = targetLang()

  candidates = synthesize(
    basename, lang, combinedVCVars,
    combinedInvAndPs + [equivalenceGrammar()],
    combinedPreds, combinedVC, combinedLoopAndPsInfo, cvcPath
  )

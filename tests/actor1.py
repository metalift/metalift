import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Or, Not, Gt, Ge, Eq, Le, Le, Sub, Synth, Call, Int, IntLit, Bool, BoolLit, FnDecl, Var, Add, Implies, Ite, Set, Tuple, TupleSel

if False:
  from synthesize_rosette import synthesize
else:
  from synthesis import synthesize_new as synthesize

def observeEquivalence(inputState, synthState):
  return Eq(
    inputState,
    Call(
      "setminus", Set(Int()),
      TupleSel(synthState, 0),
      TupleSel(synthState, 1)
    )
  )

def supportedCommand(synthState, args):
  add = args[0]
  value = args[1]

  return Ite(
    Eq(add, IntLit(1)),
    # insertion works if the elem is not in the deletion set
    Not(Call("member", Bool(), value, TupleSel(synthState, 1))),
    # deletion always works
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
      Call("union", Set(Int()), setIn, setIn)
    )

    chosenTransform = Ite(
      condition,
      setTransform,
      setTransform
    )

    summary = Eq(outputState, Call(
      "tuple",
      Tuple(Set(Int()), Set(Int())),
      chosenTransform,
      chosenTransform
    ))

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

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

    synthStateType = Tuple(Set(Int()), Set(Int()))
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
        supportedCommand(beforeStateForPS, origArgs[1:]),
        observeEquivalence(beforeState, beforeStateForPS)
      ),
      Implies(
        ps,
        observeEquivalence(afterState, afterStateForPS)
      )
    ), ps.operands[2:]

  (vcVarsStateTransition, invAndPsStateTransition, predsStateTransition, vcStateTransition, loopAndPsInfoStateTransition) = analyze(
    filename, fnNameBase + "_next_state", loopsFile,
    wrapSummaryCheck=summaryWrapStateTransition
  )

  vcVarsStateTransition = vcVarsStateTransition.union(extraVarsStateTransition)

  print("====== synthesis")
  invAndPsStateTransition = [grammar(ci) for ci in loopAndPsInfoStateTransition]

  lang = targetLang()

  candidates = synthesize(basename, lang, vcVarsStateTransition, invAndPsStateTransition, predsStateTransition, vcStateTransition, loopAndPsInfoStateTransition, cvcPath)

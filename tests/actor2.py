import os
import sys

from analysis import CodeInfo, analyze
from ir import Choose, And, Or, Not, Gt, Ge, Eq, Le, Le, Sub, Synth, Call, Int, IntLit, Bool, BoolLit, FnDecl, Var, Add, Implies, Ite, Set, Tuple, TupleSel

if False:
  from synthesize_rosette import synthesize
else:
  from synthesis import synthesize_new as synthesize

synthStateType = Tuple(Int(), Int())

# todo: synthesize so that equivalence implies equal queries
# todo: think through why equivalence needs to be synthesized
# separately from query implementations
def observeEquivalence(inputState, synthState):
  return Eq(
    inputState,
    Call(
      "-", Int(),
      TupleSel(synthState, 0),
      TupleSel(synthState, 1)
    )
  )

def stateInvariant(synthState):
  return BoolLit(True)

def supportedCommand(synthState, args):
  add = args[0]

  return Ite(
    Eq(add, IntLit(1)),
    BoolLit(True),
    Call(">", Bool(), TupleSel(synthState, 0), TupleSel(synthState, 1))
  )

def grammar(ci: CodeInfo):
  name = ci.name

  if name.startswith("inv"):
    raise Exception("no invariant")
  else:  # ps
    inputState = ci.readVars[0]
    stateVal1 = TupleSel(inputState, 0)
    stateVal2 = TupleSel(inputState, 1)

    inputAdd = ci.readVars[1]

    outputState = ci.modifiedVars[0]

    condition = Eq(inputAdd, Choose(
      IntLit(0),
      IntLit(1)
    ))

    intLit = Choose(IntLit(0), IntLit(1))

    intIn = Choose(
      stateVal1, stateVal2
    )

    intTransform = Choose(
      intIn,
      Add(
        intIn,
        # intLit # (doesn't work)
        IntLit(1) # works???
      )
    )

    chosenTransform = Choose(
      intTransform,
      Ite(
        condition,
        intTransform,
        intTransform
      )
    )

    summary = Eq(outputState, Call(
      "tuple",
      Tuple(Int(), Int()),
      chosenTransform,
      chosenTransform
    ))

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

def initState():
  return Call(
    "tuple",
    Tuple(Int(), Int()),
    IntLit(0),
    IntLit(0)
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

  candidates = synthesize(basename, lang, combinedVCVars, combinedInvAndPs, combinedPreds, combinedVC, combinedLoopAndPsInfo, cvcPath)

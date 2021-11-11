import sys
import os

from analysis import analyze
from ir import *

def observeEquivalence(inputState, synthState):
  return Call(
    "equivalence",
    Bool(),
    inputState,
    synthState
  )

def stateInvariant(synthState):
  return Call(
    "stateInvariant",
    Bool(),
    synthState
  )

def synthesize_actor(
  synthStateType, initState,
  grammarStateInvariant, supportedCommand,
  grammar, grammarQuery, grammarEquivalence,
  targetLang,
  synthesize
):
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
    ), list(ps.operands[2:])

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
    ), list(ps.operands[2:])

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
  invAndPsEquivalence = [grammarEquivalence()]
  # end equivalence

  # begin state invariant
  invAndPsStateInvariant = [grammarStateInvariant()]
  # end state invariant

  print("====== synthesis")
  
  combinedVCVars = vcVarsStateTransition.union(vcVarsQuery).union(extraVarsInitstateInvariantVC)

  combinedInvAndPs = invAndPsStateTransition + invAndPsQuery + invAndPsEquivalence + invAndPsStateInvariant

  combinedPreds = predsStateTransition + predsQuery

  combinedLoopAndPsInfo = loopAndPsInfoStateTransition + loopAndPsInfoQuery + invAndPsEquivalence + invAndPsStateInvariant
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

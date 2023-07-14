from typing import List

from mypy.nodes import Statement

from metalift.frontend.python import Driver
from metalift.ir import (Add, And, Call, Choose, Eq, Expr, FnDecl, FnDeclRecursive,
                         Int, IntLit, Ite, Lt, Mul, Sub, Tuple, TupleGet,
                         TupleT, Var)
from metalift.rosette_translator import toRosette
from tests.python.utils.utils import codegen

UNINTERP_FN_NAME = "uninterp"

def uninterp(x: Var, y: Var):
    return Call(UNINTERP_FN_NAME, Int(), x, y)

def target_lang() -> List[FnDeclRecursive]:
    x = Var("x", Int())
    y = Var("y", Int())
    uninterp = FnDeclRecursive(UNINTERP_FN_NAME, Int(), None, x, y)
    return [uninterp]


def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    x, y = reads
    return Eq(ret_val, Add(uninterp(x, x), uninterp(y, y)))

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    raise Exception("no loop in the source")

if __name__ == "__main__":
    filename = "tests/python/uninterp.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar, uninterp_fns=[UNINTERP_FN_NAME])

    i = driver.variable("i", Int())
    j = driver.variable("j", Int())

    test(i, j)

    synthDir = "./synthesisLogs/"
    synthFile = synthDir + "uninterp" + ".rkt"

    lang = target_lang()

    synths = [i.gen_Synth() for i in driver.inv_tracker.predicates.values()]
    inv_guess = []
    toRosette(
        filename=synthFile,
        targetLang=lang,
        vars=set(driver.var_tracker.all()),
        invAndPs=synths,
        preds=[],
        vc=And(*driver.asserts),
        loopAndPsInfo=synths,
        invGuess=inv_guess,
        unboundedInts=False,
        listBound=2
    )

    exit(0)


    ### SMT
    print("====== verification")

    #####identifying call sites for inlining #####
    inCalls: typing.List[typing.Any] = []
    fnCalls: typing.List[typing.Any] = []

    ##### generating function definitions of all the functions to be synthesized#####
    candidatesSMT = []
    candidateDict = {}
    r = Var("tmp9", Int())
    x = Var("arg", Int())
    y = Var("arg1", Int())
    # pretend that we have run synthesis and insert the result into candidateDict to print
    candidateDict[fnName] = summary(r, x, y)

    for ce in loopAndPsInfo:
        allVars = (
            ce.modifiedVars + ce.readVars if isinstance(ce, CodeInfo) else ce.args[2:]
        )
        ceName = ce.name if isinstance(ce, CodeInfo) else ce.args[0]
        candidatesSMT.append(
            FnDeclRecursive(
                ceName,
                ce.retT if isinstance(ce, CodeInfo) else ce.type,
                candidateDict[ceName],
                *allVars,
            )
        )

    verifFile = synthDir + basename + ".smt"

    toSMT(lang, vars, candidatesSMT, preds, vc, verifFile, inCalls, fnCalls)


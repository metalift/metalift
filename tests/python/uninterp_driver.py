from typing import Any, List

from mypy.nodes import Statement

from metalift.frontend.python import Driver
from metalift.ir import (Add, And, Call, Choose, Eq, Expr, FnDecl, FnDeclRecursive,
                         Int, IntLit, Ite, Lt, Mul, Sub, Tuple, TupleGet,
                         TupleT, Var)
from metalift.rosette_translator import toRosette
from metalift.smt_util import toSMT
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

    vars = set(driver.var_tracker.all())

    synths = [i.gen_Synth() for i in driver.inv_tracker.predicates.values()]
    preds = [] # TODO: add type
    vc = And(*driver.asserts)
    inv_guess = []
    toRosette(
        filename=synthFile,
        targetLang=lang,
        vars=vars,
        invAndPs=synths,
        preds=preds,
        vc=vc,
        loopAndPsInfo=synths,
        invGuess=inv_guess,
        unboundedInts=False,
        listBound=2
    )


    ### SMT
    print("====== verification")

    #####identifying call sites for inlining #####
    inCalls: List[Any] = []
    fnCalls: List[Any] = []

    ##### generating function definitions of all the functions to be synthesized#####
    candidatesSMT = []
    candidateDict = {}
    ret_val = Var("test_rv", Int())
    x = Var("x", Int())
    y = Var("y", Int())
    # pretend that we have run synthesis and insert the result into candidateDict to print
    candidateDict["test_ps"] = Eq(ret_val, Add(uninterp(x, x), uninterp(y, y)))

    for synth in synths:
        all_vars = synth.args[2:]
        ce_name = synth.args[0]
        candidatesSMT.append(
            FnDeclRecursive(
                ce_name,
                synth.body(),
                candidateDict[ce_name],
                *all_vars,
            )
        )

    verif_file = synthDir + "test" + ".smt"

    toSMT(
        targetLang=lang,
        vars=vars,
        invAndPs=candidatesSMT,
        preds=preds,
        vc=vc,
        outFile=verif_file,
        inCalls=[],
        fnCalls=[]
    )


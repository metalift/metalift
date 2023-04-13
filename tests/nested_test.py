from itertools import filterfalse
import os
import sys
from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.synthesize_rosette import synthesize

"""
nested list functions can be called using
Call("list_list_empty", List(List(Int())))
Call("list_list_length", Int(), args)
Call("list_list_get", List(List(Int())), args)
Call("list_list_append", List(List(Int())), args)
"""


def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):
        pass
    elif name.startswith("test"):  # ps
        pass
    else:
        raise Exception(f"Unknown function {name}")


if __name__ == "__main__":
    filename = "tests/nested_test.ll"
    basename = "fit2"

    fnName = "test"
    loopsFile = "tests/nested_test.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]
    lang = []
    candidates = synthesize(
        basename,
        lang,
        vars,
        invAndPs,
        preds,
        vc,
        loopAndPsInfo,
        cvcPath,
        noVerify=True,
    )

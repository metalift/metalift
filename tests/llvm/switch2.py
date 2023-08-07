from metalift.analysis import analyze


if __name__ == "__main__":
    filename = "tests/llvm/switch2.ll"
    basename = "switch2"

    fnName = "test"
    loopsFile = "tests/llvm/switch2.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)
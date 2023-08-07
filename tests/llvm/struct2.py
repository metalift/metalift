from metalift.analysis import analyze


if __name__ == "__main__":
    filename = "tests/llvm/struct2.ll"
    basename = "struct2"

    fnName = "test"
    loopsFile = "tests/llvm/struct2.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)
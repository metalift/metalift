from importlib import resources
import subprocess

import os
from metalift import utils
from metalift.analysis import CodeInfo
from metalift.ir import *
from metalift.rosette.rosette_translator import toRosette
from metalift.rosette.parse_candidate import parseOutput, toExpr, generateAST
from metalift.synthesis_common import (
    SynthesisFailed,
    VerificationFailed,
    generateTypes,
    verify_synth_result,
)
from metalift import process_tracker

import typing
from typing import Any, Callable, Dict, Union, IO


def toSynthesize(
    loopAndPsInfo: typing.List[Union[CodeInfo, Expr]], lang: typing.List[Expr]
) -> typing.List[str]:
    synthNames = []
    for i in loopAndPsInfo:
        if isinstance(i, CodeInfo):
            synthNames.append(i.name)
        else:
            synthNames.append(i.args[0])
    for l in lang:
        if l.args[1] == None:
            synthNames.append(l.args[0])
    return synthNames


def synthesize(
    basename: str,
    targetLang: typing.List[Expr],
    vars: typing.Set[Expr],
    invAndPs: typing.List[Expr],
    preds: typing.List[Expr],
    vc: Expr,
    loopAndPsInfo: typing.List[Union[CodeInfo, Expr]],
    cvcPath: str,
    uid: int = 0,
    noVerify: bool = False,
    unboundedInts: bool = False,
    optimize_vc_equality: bool = False,
    listBound: int = 2,
) -> typing.List[Expr]:
    invGuess: typing.List[Any] = []
    synthDir = "./synthesisLogs/"
    if not os.path.exists(synthDir):
        os.mkdir(synthDir)

    while True:
        synthFile = synthDir + basename + f"_{uid}" + ".rkt"

        with open(synthDir + "utils.rkt", "w") as out:
            out.write(resources.read_text(utils, "utils.rkt"))
        with open(synthDir + "bounded.rkt", "w") as out:
            out.write(resources.read_text(utils, "bounded.rkt"))

        if optimize_vc_equality:
            prev_vc = vc.toSMT()
            new_vars: typing.Set[Expr] = set()
            while True:
                expr_count: Dict[str, int] = {}
                vc.countVariableUses(expr_count)

                vc = vc.optimizeUselessEquality(expr_count, new_vars)

                if vc.toSMT() == prev_vc:
                    break  # run to fixpoint
                else:
                    prev_vc = vc.toSMT()

            vars = vars.union(new_vars)
            for var in list(vars):
                if var.args[0] not in expr_count:
                    vars.remove(var)
        else:
            vc = vc.simplify()

        ##### synthesis procedure #####
        choices: Dict[str, Dict[str, Expr]] = {}
        toRosette(
            synthFile,
            targetLang,
            vars,
            invAndPs,
            preds,
            vc,
            loopAndPsInfo,
            invGuess,
            unboundedInts,
            listBound,
            choices,
        )

        synthNames = toSynthesize(loopAndPsInfo, targetLang)
        procSynthesis = subprocess.Popen(
            ["racket", synthFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        process_tracker.all_processes.append(procSynthesis)

        try:
            resultSynth = [
                l.decode("utf-8").rstrip("\n")
                for l in typing.cast(IO[bytes], procSynthesis.stdout).readlines()
            ]

            exitCode = procSynthesis.wait()
            if exitCode != 0:
                if len(resultSynth) > 0 and resultSynth[0] == "#f":
                    raise SynthesisFailed(f"Synthesis failed: exit code {exitCode}")
                else:
                    raise Exception(f"Rosette failed: exit code {exitCode}")

            ##### End of Synthesis #####

            #####parsing output of rosette synthesis#####
            varTypes = {}
            for i in loopAndPsInfo:
                if isinstance(i, CodeInfo):
                    varTypes[i.name] = generateTypes(
                        i.modifiedVars + i.readVars + list(vars)
                    )
                else:
                    varTypes[i.args[0]] = generateTypes(i.args[2:])
            for l_i in targetLang:
                varTypes[l_i.args[0]] = generateTypes(l_i.args[2:])

            if resultSynth[0] == "#t":
                output = parseOutput(resultSynth[1:])
                candidateDict = {}
                fnsType = generateTypes(targetLang)
                for synthFun in invAndPs:
                    allVars = synthFun.args[2:]
                    ceName = synthFun.args[0]
                    fnsType[ceName] = Fn(
                        synthFun.args[1].type,
                        *[v.type for v in allVars],
                    )
                for n in synthNames:
                    for r in output:
                        if "define (" + n in r:
                            startIndex = r.find("(")
                            candidateDict[n] = toExpr(
                                generateAST(r[startIndex:])[0],
                                fnsType,
                                varTypes[n],
                                choices[n] if n in choices else {},
                            )
            else:
                raise SynthesisFailed("Synthesis failed")
            #####candidateDict --> definitions of all functions to be synthesized#####

            ##### generating function definitions of all the functions to be synthesized#####
            candidatesSMT = []
            for synthFun in invAndPs:
                allVars = synthFun.args[2:]
                ceName = synthFun.args[0]

                if ceName not in candidateDict:
                    # Rosette will not return a function if no choice needs to be made
                    candidateDict[ceName] = synthFun.args[1]

                candidatesSMT.append(
                    FnDecl(
                        ceName,
                        synthFun.args[1].type,
                        candidateDict[ceName],
                        *allVars,
                    )
                )

            ##### verification of synthesized ps/inv
            print("====== verification")

            verifyLogs: typing.List[str] = []

            if noVerify:
                print("Not verifying solution")
                resultVerify = "unsat"
            else:
                try:
                    resultVerify, verifyLogs = verify_synth_result(
                        basename,
                        targetLang,
                        vars,
                        preds,
                        vc,
                        loopAndPsInfo,
                        cvcPath,
                        synthDir,
                        candidatesSMT,
                        candidateDict,
                        fnsType,
                        uid,
                        useRosette=False,
                    )
                except CVC5UnsupportedException:
                    print("WARNING: USING LARGE BOUND ROSETTE FOR VERIFICATION")
                    resultVerify, verifyLogs = verify_synth_result(
                        basename,
                        targetLang,
                        vars,
                        preds,
                        vc,
                        loopAndPsInfo,
                        cvcPath,
                        synthDir,
                        candidatesSMT,
                        candidateDict,
                        fnsType,
                        uid,
                        useRosette=True,
                    )

            print("Verification Output:", resultVerify)
            if resultVerify == "unsat":
                print(
                    "Verified PS and INV Candidates ",
                    "\n\n".join([str(c) for c in candidatesSMT]),
                )
                return candidatesSMT
            else:
                print(
                    "verification failed",
                    "\n\n".join([str(c) for c in candidatesSMT]),
                )
                print("\n".join(verifyLogs))
                invGuess.append(resultSynth[1])
                print(invGuess)
                raise VerificationFailed("Verification failed")
        finally:
            procSynthesis.terminate()
            procSynthesis.wait()

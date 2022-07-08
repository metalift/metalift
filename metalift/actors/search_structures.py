from __future__ import annotations

import multiprocessing as mp
import multiprocessing.pool
import queue
from time import time
import traceback
import typing

from metalift.actors.lattices import Lattice
from metalift.analysis import CodeInfo
from metalift import process_tracker
from metalift import ir
from metalift.ir import Expr, FnDecl
from metalift.actors.synthesis import SynthesizeFun, synthesize_actor
from metalift.synthesis_common import SynthesisFailed

from typing import Any, Callable, Iterator, List, Optional, Tuple


def synthesize_crdt(
    queue: queue.Queue[Tuple[int, Any, Optional[List[FnDecl]]]],
    synthStateStructure: List[Lattice],
    initState: Callable[[Any], Expr],
    grammarStateInvariant: Callable[[Expr, Any, int], Expr],
    grammarSupportedCommand: Callable[[Expr, Any, Any, int], Expr],
    inOrder: Callable[[Any, Any], Expr],
    opPrecondition: Callable[[Any], Expr],
    grammar: Callable[[CodeInfo, Any], ir.Synth],
    grammarQuery: Callable[[CodeInfo], ir.Synth],
    grammarEquivalence: Callable[[Expr, Expr, List[ir.Var]], Expr],
    targetLang: Callable[
        [], List[typing.Union[FnDecl, ir.FnDeclNonRecursive, ir.Axiom]]
    ],
    synthesize: SynthesizeFun,
    useOpList: bool,
    stateTypeHint: Optional[ir.Type],
    opArgTypeHint: Optional[List[ir.Type]],
    queryArgTypeHint: Optional[List[ir.Type]],
    queryRetTypeHint: Optional[ir.Type],
    filename: str,
    fnNameBase: str,
    loopsFile: str,
    cvcPath: str,
    uid: int,
) -> None:
    synthStateType = ir.TupleT(*[a.ir_type() for a in synthStateStructure])

    try:
        queue.put(
            (
                uid,
                synthStateStructure,
                synthesize_actor(
                    filename,
                    fnNameBase,
                    loopsFile,
                    cvcPath,
                    synthStateType,
                    lambda: initState(synthStateStructure),
                    lambda s, b: grammarStateInvariant(s, synthStateStructure, b),
                    lambda s, a, b: grammarSupportedCommand(
                        s, a, synthStateStructure, b
                    ),
                    inOrder,
                    opPrecondition,
                    lambda ci: grammar(ci, synthStateStructure),
                    grammarQuery,
                    grammarEquivalence,
                    targetLang,
                    synthesize,
                    uid=uid,
                    useOpList=useOpList,
                    stateTypeHint=stateTypeHint,
                    opArgTypeHint=opArgTypeHint,
                    queryArgTypeHint=queryArgTypeHint,
                    queryRetTypeHint=queryRetTypeHint,
                    log=False,
                ),
            )
        )
    except SynthesisFailed:
        queue.put((uid, synthStateStructure, None))
    except:
        traceback.print_exc()
        queue.put((uid, synthStateStructure, None))


def search_crdt_structures(
    initState: Callable[[Any], Expr],
    grammarStateInvariant: Callable[[Expr, Any, int], Expr],
    grammarSupportedCommand: Callable[[Expr, Any, Any, int], Expr],
    inOrder: Callable[[Any, Any], Expr],
    opPrecondition: Callable[[Any], Expr],
    grammar: Callable[[CodeInfo, Any], ir.Synth],
    grammarQuery: Callable[[CodeInfo], ir.Synth],
    grammarEquivalence: Callable[[Expr, Expr, List[ir.Var]], Expr],
    targetLang: Callable[
        [], List[typing.Union[FnDecl, ir.FnDeclNonRecursive, ir.Axiom]]
    ],
    synthesize: SynthesizeFun,
    filename: str,
    fnNameBase: str,
    loopsFile: str,
    cvcPath: str,
    useOpList: bool,
    structureCandidates: Iterator[Any],
    reportFile: str,
    stateTypeHint: Optional[ir.Type] = None,
    opArgTypeHint: Optional[List[ir.Type]] = None,
    queryArgTypeHint: Optional[List[ir.Type]] = None,
    queryRetTypeHint: Optional[ir.Type] = None,
) -> None:
    q: queue.Queue[Tuple[int, Any, Optional[List[Expr]]]] = queue.Queue()
    queue_size = 0
    next_uid = 0

    next_res_type = None
    next_res = None

    start_times = {}

    try:
        with multiprocessing.pool.ThreadPool() as pool:
            with open(reportFile, "w") as report:
                while True:
                    while queue_size < (mp.cpu_count() // 2):
                        next_structure_type = next(structureCandidates, None)
                        if next_structure_type is None:
                            break
                        else:

                            def error_callback(e: BaseException) -> None:
                                raise e

                            try:
                                synthStateType = ir.TupleT(
                                    *[a.ir_type() for a in next_structure_type]
                                )
                                synthesize_actor(
                                    filename,
                                    fnNameBase,
                                    loopsFile,
                                    cvcPath,
                                    synthStateType,
                                    lambda: initState(next_structure_type),
                                    lambda s, b: grammarStateInvariant(
                                        s, next_structure_type, b
                                    ),
                                    lambda s, a, b: grammarSupportedCommand(
                                        s, a, next_structure_type, b
                                    ),
                                    inOrder,
                                    opPrecondition,
                                    lambda ci: grammar(ci, next_structure_type),
                                    grammarQuery,
                                    grammarEquivalence,
                                    targetLang,
                                    synthesize,
                                    uid=next_uid,
                                    useOpList=useOpList,
                                    stateTypeHint=stateTypeHint,
                                    opArgTypeHint=opArgTypeHint,
                                    queryArgTypeHint=queryArgTypeHint,
                                    queryRetTypeHint=queryRetTypeHint,
                                    log=False,
                                    skipSynth=True,
                                )
                            except KeyError:
                                # this is due to a grammar not being able to find a value
                                continue

                            print(f"Enqueueing #{next_uid} (structure: {next_structure_type})")
                            start_times[next_uid] = time()
                            pool.apply_async(
                                synthesize_crdt,
                                args=(
                                    q,
                                    next_structure_type,
                                    initState,
                                    grammarStateInvariant,
                                    grammarSupportedCommand,
                                    inOrder,
                                    opPrecondition,
                                    grammar,
                                    grammarQuery,
                                    grammarEquivalence,
                                    targetLang,
                                    synthesize,
                                    useOpList,
                                    stateTypeHint,
                                    opArgTypeHint,
                                    queryArgTypeHint,
                                    queryRetTypeHint,
                                    filename,
                                    fnNameBase,
                                    loopsFile,
                                    cvcPath,
                                    next_uid,
                                ),
                                error_callback=error_callback,
                            )
                            next_uid += 1
                            queue_size += 1

                    if queue_size == 0:
                        raise Exception("no more structures")
                    else:
                        (ret_uid, next_res_type, next_res) = q.get(
                            block=True, timeout=None
                        )
                        time_took = time() - start_times[ret_uid]
                        report.write(
                            f'{ret_uid},{time_took},"{str(next_res_type)}",{next_res != None}\n'
                        )
                        report.flush()
                        queue_size -= 1
                        if next_res != None:
                            break
                        else:
                            print(
                                f"Failed to synthesize #{ret_uid} (structure: {next_res_type})"
                            )

        if next_res == None:
            raise Exception("Synthesis failed")
        else:
            print(
                "\n========================= SYNTHESIS COMPLETE =========================\n"
            )
            print("State Structure:", next_res_type)
            print("\nRuntime Logic:")
            print("\n\n".join([c.toRosette() for c in next_res]))  # type: ignore
    finally:
        for p in process_tracker.all_processes:
            print("Terminating process", p.pid)
            p.terminate()
        process_tracker.all_processes = []

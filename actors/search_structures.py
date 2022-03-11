from __future__ import annotations

import multiprocessing as mp
import multiprocessing.pool
import queue

from analysis import CodeInfo
import process_tracker
import ir
from ir import Expr
from actors.synthesis import SynthesizeFun, synthesize_actor

from typing import Any, Callable, Iterator, List, Optional, Tuple


def synthesize_crdt(
    queue: queue.Queue[Tuple[Any, Optional[List[Expr]]]],
    synthStateStructure: Any,
    initState: Callable[[Any], Expr],
    grammarStateInvariant: Callable[[Expr], Expr],
    grammarSupportedCommand: Callable[[Expr, Any], Expr],
    inOrder: Callable[[Any, Any], Expr],
    grammar: Callable[[CodeInfo, Any], Expr],
    grammarQuery: Callable[[CodeInfo], Expr],
    grammarEquivalence: Callable[[Expr, Expr], Expr],
    targetLang: Callable[[], List[Expr]],
    synthesize: SynthesizeFun,
    useOpList: bool,
    filename: str,
    fnNameBase: str,
    loopsFile: str,
    cvcPath: str,
    uid: int,
) -> None:
    synthStateType = ir.Tuple(*[a[0] for a in synthStateStructure])

    try:
        queue.put(
            (
                synthStateType,
                synthesize_actor(
                    filename,
                    fnNameBase,
                    loopsFile,
                    cvcPath,
                    synthStateType,
                    lambda: initState(synthStateStructure),
                    grammarStateInvariant,
                    grammarSupportedCommand,
                    inOrder,
                    lambda ci: grammar(ci, synthStateStructure),
                    grammarQuery,
                    grammarEquivalence,
                    targetLang,
                    synthesize,
                    uid=uid,
                    useOpList=useOpList,
                    log=False,
                ),
            )
        )
    except:
        import traceback

        traceback.print_exc()
        queue.put((synthStateType, None))


def search_crdt_structures(
    initState: Callable[[Any], Expr],
    grammarStateInvariant: Callable[[Expr], Expr],
    grammarSupportedCommand: Callable[[Expr, Any], Expr],
    inOrder: Callable[[Any, Any], Expr],
    grammar: Callable[[CodeInfo, Any], Expr],
    grammarQuery: Callable[[CodeInfo], Expr],
    grammarEquivalence: Callable[[Expr, Expr], Expr],
    targetLang: Callable[[], List[Expr]],
    synthesize: SynthesizeFun,
    filename: str,
    fnNameBase: str,
    loopsFile: str,
    cvcPath: str,
    useOpList: bool,
    structureCandidates: Iterator[Any],
) -> None:
    q: queue.Queue[Tuple[Any, Optional[List[Expr]]]] = queue.Queue()
    queue_size = 0
    uid = 0

    next_res_type = None
    next_res = None

    try:
        with multiprocessing.pool.ThreadPool() as pool:
            while True:
                while queue_size < (mp.cpu_count() // 2):
                    next_structure_type = next(structureCandidates, None)
                    if next_structure_type is None:
                        break
                    else:
                        print(
                            f"Enqueueing #{uid}:", [t[0] for t in next_structure_type]
                        )

                        def error_callback(e: BaseException) -> None:
                            raise e

                        pool.apply_async(
                            synthesize_crdt,
                            args=(
                                q,
                                next_structure_type,
                                initState,
                                grammarStateInvariant,
                                grammarSupportedCommand,
                                inOrder,
                                grammar,
                                grammarQuery,
                                grammarEquivalence,
                                targetLang,
                                synthesize,
                                useOpList,
                                filename,
                                fnNameBase,
                                loopsFile,
                                cvcPath,
                                uid,
                            ),
                            error_callback=error_callback,
                        )
                        uid += 1
                        queue_size += 1

                if queue_size == 0:
                    raise Exception("no more structures")
                else:
                    (next_res_type, next_res) = q.get(block=True, timeout=None)
                    queue_size -= 1
                    if next_res != None:
                        break
                    else:
                        print("Failed to synthesize with structure", next_res_type)

        if next_res == None:
            raise Exception("Synthesis failed")
        else:
            print(
                "\n========================= SYNTHESIS COMPLETE =========================\n"
            )
            print("State Structure:", next_res_type)
            print("\nRuntime Logic:")
            print("\n\n".join([c.toSMT() for c in next_res]))  # type: ignore
    finally:
        for p in process_tracker.all_processes:
            p.terminate()

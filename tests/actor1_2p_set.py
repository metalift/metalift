from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import multiprocessing as mp
import queue
import process_tracker

from synthesize_auto import synthesize


def grammarEquivalence(inputState, synthState):
    return auto_grammar(Bool(), 2, inputState, synthState, enable_sets=True)


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), 1, synthState, enable_sets=True)


def grammarSupportedCommand(synthState, args):
    add = args[0]

    return Ite(
        Eq(add, IntLit(1)),
        auto_grammar(Bool(), 1, synthState, enable_sets=True),
        auto_grammar(Bool(), 1, synthState, enable_sets=True),
    )


def inOrder(arg1, arg2):
    # removes win
    return Ite(
        Eq(arg1[0], IntLit(1)),  # if first command is insert
        BoolLit(True),  # second can be insert or remove
        Not(Eq(arg2[0], IntLit(1))),  # but if remove, must be remove next
    )


def grammarQuery(ci: CodeInfo):
    name = ci.name

    setContainTransformed = auto_grammar(Bool(), 3, *ci.readVars, enable_sets=True)

    summary = Ite(setContainTransformed, IntLit(1), IntLit(0))

    return Synth(name, summary, *ci.readVars)


def grammar(ci: CodeInfo, synthStateStructure):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]

        condition = Eq(inputAdd, IntLit(1))

        summary = MakeTuple(
            *[
                synthStateStructure[i][1](
                    TupleGet(inputState, IntLit(i)),
                    Ite(
                        condition,
                        auto_grammar(TupleGet(inputState, IntLit(i)).type, 1, inputValue, enable_sets=True),
                        auto_grammar(TupleGet(inputState, IntLit(i)).type, 1, inputValue, enable_sets=True),
                    )
                )
                for i in range(len(synthStateStructure))
            ],
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState(synthStateStructure):
    return MakeTuple(
        *[elem[2] for elem in synthStateStructure]
    )

def targetLang():
    return []


def synthesize_crdt(queue, synthStateStructure, useOpList, filename, fnNameBase, loopsFile, cvcPath, uid):
    synthStateType = Tuple(*[a[0] for a in synthStateStructure])

    try:
        queue.put((synthStateType, synthesize_actor(
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
        )))
    except Exception as e:
        queue.put((synthStateType, None))

if __name__ == "__main__":
    mode = sys.argv[1]
    filename = sys.argv[2]
    fnNameBase = sys.argv[3]
    loopsFile = sys.argv[4]
    cvcPath = sys.argv[5]

    if mode == "aci":
        check_aci(
            filename,
            fnNameBase,
            loopsFile,
            cvcPath,
        )
    else:
        useOpList = False
        if mode == "synth-oplist":
            useOpList = True

        structureCandidates = iter([
            [lat.MaxInt, lat.MaxInt],
            [lat.Set(Int()), lat.Set(Int())],
            [lat.Set(Int()), lat.Set(Int()), lat.Set(Int())],
        ])

        m = mp.Manager()
        q = queue.Queue()
        queue_size = 0
        uid = 0

        next_res_type = None
        next_res = None

        try:
            with mp.pool.ThreadPool() as pool:
                while True:
                    while queue_size < mp.cpu_count():
                        next_structure_type = next(structureCandidates, None)
                        if next_structure_type is None:
                            break
                        else:
                            print("Enqueueing", next_structure_type)
                            def error_callback(e):
                                raise e
                            pool.apply_async(synthesize_crdt,
                                args=(q, next_structure_type, useOpList, filename, fnNameBase, loopsFile, cvcPath, uid),
                                error_callback=error_callback
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

            print("\n========================= SYNTHESIS COMPLETE =========================\n")
            print("State Structure:", next_res_type)
            print("\nRuntime Logic:")
            print("\n\n".join([c.toSMT() for c in next_res]))
        finally:
            for p in process_tracker.all_processes:
                p.terminate()

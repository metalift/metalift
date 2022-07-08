from time import time
from crdt_synthesis.search_structures import search_crdt_structures
from metalift.analysis import CodeInfo
from metalift.ir import *
import crdt_synthesis.lattices as lat
from crdt_synthesis.auto_grammar import all_node_id_gets, auto_grammar, expand_lattice_logic
import sys
from metalift.maps_lang import mapsLang

from metalift.synthesize_auto import synthesize

base_depth = 1

def fold_conditions(out, conditions):
    for c in conditions:
        out = Ite(c, out, out)
    return out

def grammarEquivalence(inputState, synthState, queryParams):
    return auto_grammar(
        Bool(),
        base_depth,
        inputState, synthState, *queryParams
    )


def grammarStateInvariant(synthState, synthStateStructure, invariantBoost):
    state_valid = And(*[
        synthStateStructure[i].check_is_valid(
            TupleGet(synthState, IntLit(i))
        )
        for i in range(len(synthStateStructure))
    ])

    return And(
        state_valid,
        auto_grammar(Bool(), base_depth + invariantBoost, synthState)
    )


def grammarSupportedCommand(synthState, args, synthStateStructure, invariantBoost):
    conditions = [Eq(a, IntLit(1)) for a in args if a.type == BoolInt()]

    out = auto_grammar(
        Bool(), base_depth + 1 + invariantBoost,
        synthState, *args,
        *expand_lattice_logic(*[
            (TupleGet(synthState, IntLit(i)), synthStateStructure[i])
            for i in range(len(synthStateStructure))
        ]),
        enable_ite=True
    )

    return fold_conditions(out, conditions)


def grammarQuery(ci: CodeInfo):
    name = ci.name

    if ci.retT == BoolInt():
        condition = auto_grammar(
            Bool(),
            base_depth + 2,
            *ci.readVars,
            allow_node_id_reductions=True,
        )

        summary = Ite(condition, IntLit(1), IntLit(0))
    else:
        summary = auto_grammar(
            parseTypeRef(ci.retT), base_depth + 2,
            *ci.readVars,
            enable_ite=True,
            allow_node_id_reductions=True,
        )

    return Synth(name, summary, *ci.readVars)


def grammar(ci: CodeInfo, synthStateStructure):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        args = ci.readVars[1:]

        conditions = [Eq(a, IntLit(1)) for a in args if a.type == BoolInt()]

        non_associative_data = []
        for a in args:
            if a.type == NodeIDInt():
                non_associative_data = all_node_id_gets(
                    inputState, a,
                    auto_grammar(None, 0, *args)
                )
                break

        out = Tuple(
            *[
                synthStateStructure[i].merge(
                    TupleGet(inputState, IntLit(i)),
                    fold_conditions(auto_grammar(
                        TupleGet(inputState, IntLit(i)).type,
                        base_depth + 1,
                        *args,
                        *non_associative_data
                    ), conditions)
                )
                for i in range(len(synthStateStructure))
            ],
        )

        return Synth(name, out, *ci.modifiedVars, *ci.readVars)


def initState(synthStateStructure):
    return Tuple(
        *[auto_grammar(elem.ir_type(), 1, elem.bottom()) for elem in synthStateStructure]
    )

def targetLang():
    return mapsLang()


benchmarks = {
    "flag_dw": {
        "ll_name": "sequential_flag",
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[1], arg2[1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[1], arg2[1]), # if clocks concurrent
                Ite(
                    Eq(arg1[0], IntLit(1)), # if first is enable
                    BoolLit(True), # second can be anything
                    Not(Eq(arg2[0], IntLit(1))), # but if remove, must be remove next
                ),
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: Ge(op[-1], IntLit(1)),
        "stateTypeHint": BoolInt(),
        "opArgTypeHint": [BoolInt(), ClockInt()],
        "queryArgTypeHint": None,
        "queryRetTypeHint": BoolInt()
    },
    "flag_ew": {
        "ll_name": "sequential_flag",
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[1], arg2[1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[1], arg2[1]), # if clocks concurrent
                Ite(
                    Eq(arg1[0], IntLit(1)), # if first is enable
                    Eq(arg2[0], IntLit(1)), # second must be enable
                    BoolLit(True), # but if remove, can be anything next
                ),
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: Ge(op[-1], IntLit(1)),
        "stateTypeHint": BoolInt(),
        "opArgTypeHint": [BoolInt(), ClockInt()],
        "queryArgTypeHint": None,
        "queryRetTypeHint": BoolInt()
    },
    "lww_register": {
        "ll_name": "sequential_register",
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[-1], arg2[-1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[-1], arg2[-1]), # if clocks concurrent
                Ge(arg2[0], arg1[0]),  # second command must have a higher value
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: And(
            Ge(op[-1], IntLit(1)),
            Ge(op[0], IntLit(0))
        ),
        "stateTypeHint": OpaqueInt(),
        "opArgTypeHint": [OpaqueInt(), ClockInt()],
        "queryArgTypeHint": [],
        "queryRetTypeHint": OpaqueInt(),
    },
    "g_set": {
        "ll_name": "sequential1",
        "inOrder": lambda arg1, arg2: Ite(
            Eq(arg1[0], IntLit(1)),  # if first command is insert
            Eq(arg2[0], IntLit(1)),  # second must be insert
            BoolLit(True),  # but if remove, can be anything next
        ),
        "opPrecondition": lambda op: BoolLit(True),
        "stateTypeHint": Set(OpaqueInt()),
        "opArgTypeHint": [BoolInt(), OpaqueInt()],
        "queryArgTypeHint": [OpaqueInt()],
        "queryRetTypeHint": BoolInt(),
    },
    "2p_set": {
        "ll_name": "sequential1",
        "inOrder": lambda arg1, arg2: Ite(
            Eq(arg1[0], IntLit(1)),  # if first command is insert
            BoolLit(True),  # second can be insert or remove
            Not(Eq(arg2[0], IntLit(1))),  # but if remove, must be remove next
        ),
        "opPrecondition": lambda op: BoolLit(True),
        "stateTypeHint": Set(OpaqueInt()),
        "opArgTypeHint": [BoolInt(), OpaqueInt()],
        "queryArgTypeHint": [OpaqueInt()],
        "queryRetTypeHint": BoolInt(),
    },
    "add_wins_set": {
        "ll_name": "sequential1_clock",
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[-1], arg2[-1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[-1], arg2[-1]), # if clocks concurrent
                Ite(
                    Eq(arg1[0], IntLit(1)),  # if first command is insert
                    Eq(arg2[0], IntLit(1)), # second command must be insert
                    BoolLit(True),  # second can be insert or remove
                ),
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: Ge(op[-1], IntLit(1)),
        "stateTypeHint": Set(OpaqueInt()),
        "opArgTypeHint": [BoolInt(), OpaqueInt(), ClockInt()],
        "queryArgTypeHint": [OpaqueInt()],
        "queryRetTypeHint": BoolInt(),
    },
    "remove_wins_set": {
        "ll_name": "sequential1_clock",
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[-1], arg2[-1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[-1], arg2[-1]), # if clocks concurrent
                Ite(
                    Eq(arg1[0], IntLit(1)),  # if first command is insert
                    BoolLit(True),  # second can be insert or remove
                    Not(Eq(arg2[0], IntLit(1))),  # but if remove, must be remove next
                ),
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: Ge(op[-1], IntLit(1)),
        "stateTypeHint": Set(OpaqueInt()),
        "opArgTypeHint": [BoolInt(), OpaqueInt(), ClockInt()],
        "queryArgTypeHint": [OpaqueInt()],
        "queryRetTypeHint": BoolInt(),
    },
    "grow_only_counter": {
        "ll_name": "sequential2",
        "inOrder": lambda arg1, arg2: And(
            Eq(arg1[0], IntLit(1)),
            Eq(arg2[0], IntLit(1))
        ),
        "opPrecondition": lambda op: Eq(op[0], IntLit(1)),
        "stateTypeHint": Int(),
        "opArgTypeHint": [BoolInt(), NodeIDInt()],
        "queryArgTypeHint": [],
        "queryRetTypeHint": Int(),
        "nonIdempotent": True,
    },
    "general_counter": {
        "ll_name": "sequential2",
        "inOrder": lambda arg1, arg2: BoolLit(True),
        "opPrecondition": lambda op: BoolLit(True),
        "stateTypeHint": Int(),
        "opArgTypeHint": [BoolInt(), NodeIDInt()],
        "queryArgTypeHint": [],
        "queryRetTypeHint": Int(),
        "nonIdempotent": True,
    }
}

def has_node_id(tup):
    for v in tup:
        if v.has_node_id():
            return True
    return False

if __name__ == "__main__":
    mode = sys.argv[1]
    bench = sys.argv[2]

    if bench == "all":
        benches = list(benchmarks.keys())
    else:
        benches = [bench]

    with open("benchmarks.csv", "w") as report:
        for bench in benches:
            bench_data = benchmarks[bench]

            filename = f"crdt_tests/{bench_data['ll_name']}.ll"
            fnNameBase = "test"
            loopsFile = f"crdt_tests/{bench_data['ll_name']}.loops"
            cvcPath = "cvc5"

            useOpList = False
            if mode == "synth-oplist":
                useOpList = True

            nonIdempotent = "nonIdempotent" in bench_data and bench_data["nonIdempotent"]
            all_structures = lat.gen_structures()
            filtered_structures = all_structures
            if nonIdempotent:
                filtered_structures = filter(has_node_id, all_structures)

            start_time = time()
            search_crdt_structures(
                initState,
                grammarStateInvariant,
                grammarSupportedCommand,
                bench_data["inOrder"],
                bench_data["opPrecondition"],
                grammar,
                grammarQuery,
                grammarEquivalence,
                targetLang,
                synthesize,
                filename, fnNameBase, loopsFile, cvcPath, useOpList,
                filtered_structures,
                reportFile=f"benchmarks-{bench}.csv",
                stateTypeHint=bench_data["stateTypeHint"],
                opArgTypeHint=bench_data["opArgTypeHint"],
                queryArgTypeHint=bench_data["queryArgTypeHint"],
                queryRetTypeHint=bench_data["queryRetTypeHint"],
            )
            end_time = time()

            print(f"{bench} took {end_time - start_time} seconds")
            report.write(f"{bench},{end_time - start_time}\n")
            report.flush()

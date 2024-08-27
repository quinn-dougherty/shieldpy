from enum import Enum
from typing import Type

from shieldpy.automata import nondeterministic_finite as nfa
from shieldpy.automata.types import Alphabet, State
from shieldpy.automata import game

import z3


def encode_state_enum(S: Type[Enum]) -> z3.Datatype:
    state = z3.Datatype("State")
    for name in S:
        state.declare(name.name)
    return state.create()


def encode_alphabet_enum(Alphabet: Type[Enum]) -> z3.Datatype:
    alphabet = z3.Datatype("Alphabet")
    for name in Alphabet:
        alphabet.declare(name.name)
    return alphabet.create()


def encode_enum_sort(S: Type[Enum]) -> z3.Datatype:
    return z3.EnumSort(S.__name__, [s.name for s in S])


def encode_nfa_transitions(
    S: Type[Enum], A: Type[Enum], transitions: set[nfa.Transition]
) -> tuple[z3.Function, z3.And, list[z3.Datatype], list[z3.Datatype]]:
    state_z3, states = encode_enum_sort(S)
    alphabet_z3, alphabets = encode_enum_sort(A)
    transition_func = z3.Function(
        "transition", state_z3, alphabet_z3, state_z3, z3.BoolSort()
    )
    constraints = []
    for t in transitions:
        s = states[t.start.value - 1]
        symb = alphabets[t.symbol.value - 1]
        output = states[t.end.value - 1]
        f = transition_func(s, symb, output)
        constraints.append(f)

    return transition_func, z3.And(constraints), states, alphabets


def encode_nfa(
    nfa: nfa.NFA,
) -> tuple[z3.Function, z3.And, list[z3.Datatype], list[z3.Datatype]]:
    return encode_nfa_transitions(nfa.states, nfa.alphabet, nfa.transitions)


def encode_enum_pairs_sort(S: tuple[Type[Enum], Type[Enum]]) -> z3.Datatype:
    return z3.EnumSort(
        f"{S[0].__name__}{S[1].__name__}", [f"{s1.name}{s2.name}" for (s1, s2) in S]
    )


def encode_safetygame_transitions(
    S: tuple[Type[Enum], Type[Enum]], A: Type[Enum], transitions: set[game.Transition]
) -> tuple[z3.Function, z3.And, list[z3.Datatype], list[z3.Datatype]]:
    state_z3, states = encode_enum_pairs_sort(S)
    alphabet_z3, alphabets = encode_enum_sort(A)
    transition_func = z3.Function(
        "transition", state_z3, alphabet_z3, state_z3, z3.BoolSort()
    )
    constraints = []
    for t in transitions:
        s = states[t.start.value - 1]
        symb = alphabets[t.symbol.value - 1]
        output = states[t.end.value - 1]
        f = transition_func(s, symb, output)
        constraints.append(f)

    return transition_func, z3.And(constraints), states, alphabets


def encode_safetygame(
    g: game.SafetyGame,
) -> tuple[z3.Function, z3.And, list[z3.Datatype], list[z3.Datatype]]:
    return encode_safetygame_transitions(g.states, g.alphabet, g.transitions)

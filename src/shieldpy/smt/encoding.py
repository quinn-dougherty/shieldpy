from enum import Enum
from typing import Type
import z3
from shieldpy.nfa import Transition, NFA, State, Alphabet


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


def encode_transitions(
    S: Type[Enum], A: Type[Enum], transitions: set[Transition]
) -> tuple[z3.Function, z3.And]:
    # state_z3 = encode_state_enum(S)
    state_z3, _ = encode_enum_sort(S)
    alphabet_z3, _ = encode_enum_sort(A)
    # alphabet_z3 = encode_alphabet_enum(Alphabet)
    transition_func = z3.Function("transition", state_z3, alphabet_z3, state_z3)
    constraints = []
    for t in transitions:
        s = state_z3.constructor(t.start.value)
        symb = alphabet_z3.constructor(t.symbol.value)
        output = state_z3.constructor(t.end.value)
        constraints.append(transition_func(s, symb, output))

    return transition_func, z3.And(constraints)

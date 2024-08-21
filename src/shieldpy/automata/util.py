from enum import Enum, auto
from shieldpy.automata.types import State, Alphabet


def create_state_enum(cardinality: int) -> State:
    return Enum("State", {f"q{i}": auto() for i in range(cardinality)})


def create_alphabet_enum(cardinality: int) -> Alphabet:
    return Enum("Alphabet", {chr(97 + i): auto() for i in range(cardinality)})

from enum import Enum, auto
from shieldpy.automata.types import State, Alphabet


def create_state_enum(cardinality: int, letter: str = "q") -> State:
    return Enum("State", {f"{letter}{i}": auto() for i in range(cardinality)})


def create_alphabet_enum(cardinality: int) -> Alphabet:
    return Enum("Alphabet", {chr(97 + i): auto() for i in range(cardinality)})

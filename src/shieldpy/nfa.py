from dataclasses import dataclass
from enum import Enum, auto
from typing import Callable

type State = Enum
type Alphabet = Enum
type Word = list[Alphabet]
type TransitionFunction = Callable[[State, Alphabet], set[State]]


def create_state_enum(cardinality: int) -> State:
    return Enum("State", {f"q{i}": auto() for i in range(cardinality)})


def create_alphabet_enum(cardinality: int) -> Alphabet:
    return Enum("Alphabet", {chr(97 + i): auto() for i in range(cardinality)})


@dataclass
class Transition:
    """
    Transition from one state to another on a symbol.

    Relational encoding, equivalent to function: State x Alphabet -> 2^State.
    """

    start: State
    symbol: Alphabet
    end: State

    def __hash__(self):
        return hash((self.start, self.symbol, self.end))


@dataclass
class NFA:
    states: State
    transitions: set[Transition]
    start: State
    accept: set[State]
    alphabet: Alphabet


def accepts(nfa: NFA, word: Word) -> bool:
    current_states = {nfa.start}

    for symbol in word:
        next_states = set()
        for state in current_states:
            for transition in nfa.transitions:
                if transition.start == state and transition.symbol == symbol:
                    next_states.add(transition.end)
        current_states = next_states

        if not current_states:
            return False

    return any(state in nfa.accept for state in current_states)

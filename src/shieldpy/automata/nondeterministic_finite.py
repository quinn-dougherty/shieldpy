from dataclasses import dataclass
from typing import FrozenSet
from shieldpy.automata.types import State, Alphabet, Word


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
    transitions: FrozenSet[Transition]
    start: State
    accept: FrozenSet[State]
    alphabet: Alphabet

    def accepts(self, word: Word) -> bool:
        current_states = {self.start}

        for symbol in word:
            next_states = set()
            for state in current_states:
                for transition in self.transitions:
                    if transition.start == state and transition.symbol == symbol:
                        next_states.add(transition.end)
            current_states = next_states

            if not current_states:
                return False

        return any(state in self.accept for state in current_states)

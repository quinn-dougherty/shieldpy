from dataclasses import dataclass
from shieldpy.automata.types import State, Alphabet

@dataclass(frozen=True)
class Transition:
    """
    Transition from one state to another on a symbol.

    Relational encoding, equivalent to function: State x Alphabet -> 2^State.
    """

    start: tuple[State, State]
    symbol: Alphabet
    end: tuple[State, State]

    def __hash__(self):
        return hash((self.start, self.symbol, self.end))


@dataclass
class SafetyGame:
    states: frozenset[tuple[State, State]]  # (NFA state, SafetyAutomaton state)
    transitions: frozenset[Transition]
    initial_states: frozenset[tuple[State, State]]
    safe_states: frozenset[tuple[State, State]]
    alphabet: frozenset[Alphabet]

    def solve(self) -> set[tuple[State, State]]:
        # Implement the safety game solving algorithm here
        # This should compute and return the winning region
        pass

from dataclasses import dataclass
from shieldpy.automata.types import State, Alphabet


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

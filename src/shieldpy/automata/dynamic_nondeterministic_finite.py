from dataclasses import dataclass, field
from typing import Set


@dataclass(frozen=True)
class State:
    name: str


@dataclass(frozen=True)
class Alphabet:
    symbol: str


Word = str


@dataclass(frozen=True)
class Transition:
    start: State
    symbol: Alphabet
    end: State

    def __hash__(self):
        return hash((self.start, self.symbol, self.end))


@dataclass
class DynamicNFA:
    states: Set[State] = field(default_factory=set)
    transitions: Set[Transition] = field(default_factory=set)
    start: State = field(default_factory=lambda: State("q0"))
    accept: Set[State] = field(default_factory=set)
    alphabet: Set[Alphabet] = field(default_factory=set)

    def __post_init__(self):
        self.states.add(self.start)

    def add_state(self, state: State):
        self.states.add(state)

    def add_symbol(self, symbol: Alphabet):
        self.alphabet.add(symbol)

    def add_transition(self, start: State, symbol: Alphabet, end: State):
        self.add_state(start)
        self.add_state(end)
        self.add_symbol(symbol)
        self.transitions.add(Transition(start, symbol, end))

    def set_accept_state(self, state: State):
        self.add_state(state)
        self.accept.add(state)

    def get_next_states(self, current_state: State, symbol: Alphabet) -> Set[State]:
        next_states = set()
        for transition in self.transitions:
            if transition.start == current_state and transition.symbol == symbol:
                next_states.add(transition.end)
        return next_states

    # TODO change the signature so it accepts an epsilon
    #
    def accepts(self, word: Word) -> bool:
        current_states = {self.start}
        for symbol in word:
            alphabet_symbol = Alphabet(symbol)
            if alphabet_symbol not in self.alphabet:
                return False
            next_states = set()
            for state in current_states:
                next_states.update(self.get_next_states(state, alphabet_symbol))
            current_states = next_states
            if not current_states:
                return False
        # Change the in to "in neighborhood of accept states"
        return any(state in self.accept for state in current_states)

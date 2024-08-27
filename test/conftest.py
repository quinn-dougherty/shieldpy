import pytest
from shieldpy.automata.util import (
    create_state_enum,
    create_alphabet_enum,
)
from shieldpy.automata import nondeterministic_finite as nfa
from shieldpy.automata.nondeterministic_finite import NFA
from shieldpy.automata import game
from shieldpy.logic.syntax import Atom, always, next_, implies

@pytest.fixture(scope="session")
def simple_state():
    return create_state_enum(3)

@pytest.fixture(scope="session")
def simple_state_2():
    return create_state_enum(3, "p")

@pytest.fixture(scope="session")
def simple_alphabet():
    return create_alphabet_enum(2)


@pytest.fixture(scope="session")
def simple_transitions(simple_state, simple_alphabet):
    return {
        nfa.Transition(simple_state.q0, simple_alphabet.a, simple_state.q0),
        nfa.Transition(simple_state.q0, simple_alphabet.b, simple_state.q0),
        nfa.Transition(simple_state.q0, simple_alphabet.a, simple_state.q1),
        nfa.Transition(simple_state.q1, simple_alphabet.b, simple_state.q2),
    }

@pytest.fixture(scope="session")
def simple_transitions_2(simple_state_2, simple_alphabet):
    return {
        nfa.Transition(simple_state_2.p0, simple_alphabet.a, simple_state_2.p0),
        nfa.Transition(simple_state_2.p0, simple_alphabet.b, simple_state_2.p0),
        nfa.Transition(simple_state_2.p0, simple_alphabet.a, simple_state_2.p1),
        nfa.Transition(simple_state_2.p1, simple_alphabet.b, simple_state_2.p2),
    }

@pytest.fixture(scope="session")
def simple_nfa(simple_state, simple_alphabet, simple_transitions):
    return (
        NFA(
            states=simple_state,
            transitions=simple_transitions,
            start=simple_state.q0,
            accept={simple_state.q2},
            alphabet=simple_alphabet,
        ),
        simple_state,
        simple_alphabet,
    )

@pytest.fixture(scope="session")
def simple_nfa_2(simple_state_2, simple_alphabet, simple_transitions_2):
    return (
        NFA(
            states=simple_state_2,
            transitions=simple_transitions_2,
            start=simple_state_2.p0,
            accept={simple_state_2.p2},
            alphabet=simple_alphabet,
        ),
        simple_state_2,
        simple_alphabet,
    )


@pytest.fixture(scope="session")
def simple_spec():
    a = Atom("a")
    b = Atom("b")
    return always(implies(a, next_(b)))

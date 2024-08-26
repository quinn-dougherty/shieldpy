import pytest
from shieldpy.automata.nondeterministic_finite import (
    Transition,
    NFA,
)
from shieldpy.automata.util import (
    create_state_enum,
    create_alphabet_enum,
)
from shieldpy.logic.syntax import Atom, always, next_, implies


@pytest.fixture(scope="session")
def simple_state():
    return create_state_enum(3)


@pytest.fixture(scope="session")
def simple_alphabet():
    return create_alphabet_enum(2)


@pytest.fixture(scope="session")
def simple_transitions(simple_state, simple_alphabet):
    return {
        Transition(simple_state.q0, simple_alphabet.a, simple_state.q0),
        Transition(simple_state.q0, simple_alphabet.b, simple_state.q0),
        Transition(simple_state.q0, simple_alphabet.a, simple_state.q1),
        Transition(simple_state.q1, simple_alphabet.b, simple_state.q2),
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
def simple_spec():
    a = Atom("a")
    b = Atom("b")
    return always(implies(a, next_(b)))

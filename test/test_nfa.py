import pytest
from shieldpy.nfa import (
    accepts,
    create_state_enum,
    create_alphabet_enum,
    Transition,
    NFA,
)


@pytest.fixture
def simple_nfa():
    State = create_state_enum(3)
    Alphabet = create_alphabet_enum(2)

    return (
        NFA(
            states=State,
            transitions={
                Transition(State.q0, Alphabet.a, State.q0),
                Transition(State.q0, Alphabet.b, State.q0),
                Transition(State.q0, Alphabet.a, State.q1),
                Transition(State.q1, Alphabet.b, State.q2),
            },
            start=State.q0,
            accept={State.q2},
            alphabet=Alphabet,
        ),
        State,
        Alphabet,
    )


def test_accepts_valid_strings(simple_nfa):
    nfa, State, Alphabet = simple_nfa
    assert accepts(nfa, [Alphabet.a, Alphabet.b])
    assert accepts(nfa, [Alphabet.a, Alphabet.a, Alphabet.b])
    assert accepts(nfa, [Alphabet.b, Alphabet.a, Alphabet.b])


def test_rejects_invalid_strings(simple_nfa):
    nfa, State, Alphabet = simple_nfa
    assert not accepts(nfa, [Alphabet.a])
    assert not accepts(nfa, [Alphabet.b])
    assert not accepts(nfa, [Alphabet.a, Alphabet.a])
    assert not accepts(nfa, [Alphabet.b, Alphabet.a])


def test_rejects_empty_string(simple_nfa):
    nfa, _, _ = simple_nfa
    assert not accepts(nfa, [])

from shieldpy.nfa import (
    accepts,
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

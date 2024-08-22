from shieldpy.watertank import watertank_nfa, WaterTankAlphabet, WaterTankState

def test_accepts_valid_strings(simple_nfa):
    nfa, State, Alphabet = simple_nfa
    assert nfa.accepts([Alphabet.a, Alphabet.b])
    assert nfa.accepts([Alphabet.a, Alphabet.a, Alphabet.b])
    assert nfa.accepts([Alphabet.b, Alphabet.a, Alphabet.b])


def test_rejects_invalid_strings(simple_nfa):
    nfa, State, Alphabet = simple_nfa
    assert not nfa.accepts([Alphabet.a])
    assert not nfa.accepts([Alphabet.b])
    assert not nfa.accepts([Alphabet.a, Alphabet.a])
    assert not nfa.accepts([Alphabet.b, Alphabet.a])


def test_rejects_empty_string(simple_nfa):
    nfa, _, _ = simple_nfa
    assert not nfa.accepts([])

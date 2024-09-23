from shieldpy.environments.watertank import watertank_nfa, WaterTankAlphabet, WaterTankState

def test_accepts_valid_strings(watertank_nfa):
    nfa, State, Alphabet = watertank_nfa
    assert nfa.accepts([])
    assert nfa.accepts([Alphabet.CLOSE_AND_OK_LEVEL])
    assert nfa.accepts([Alphabet.OPEN_AND_OK_LEVEL])
    assert nfa.accepts([Alphabet.OPEN_AND_OK_LEVEL, Alphabet.OPEN_AND_OK_LEVEL, Alphabet.OPEN_AND_OK_LEVEL, Alphabet.OPEN_AND_OK_LEVEL])


def test_accepts_valid_strings(watertank_nfa):
    nfa, State, Alphabet = watertank_nfa
    assert not nfa.accepts([Alphabet.OPEN_AND_OK_LEVEL, Alphabet.CLOSE_AND_OK_LEVEL])

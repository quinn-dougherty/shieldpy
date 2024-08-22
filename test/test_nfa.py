def test_accepts_valid_strings(watertank_nfa):
    nfa, WaterTankState, WaterTankAlphabet = watertank_nfa
    assert nfa.accepts([])
    assert nfa.accepts([])
    assert nfa.accepts([])

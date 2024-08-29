import pytest
from shieldpy.automata.util import create_state_enum
from shieldpy.automata.game import SafetyGame, Transition
from shieldpy.automata.product import product

def test_product(simple_nfa, simple_nfa_2):
    nfa1, _, _ = simple_nfa
    nfa2, _, _ = simple_nfa_2
    game = product(nfa1, nfa2)
    assert len(game.states) == 9

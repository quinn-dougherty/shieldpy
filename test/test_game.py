import pytest
from shieldpy.automata.util import create_state_enum
from shieldpy.automata.game import SafetyGame, Transition
from shieldpy.automata.product import product

def test_product(simple_nfa, simple_nfa_2):
    game = product(simple_nfa, simple_nfa_2)
    assert len(game.states) == 9

import pytest
import z3
from shieldpy.compiler import compile_spec
from shieldpy.automata.nondeterministic_finite import NFA
from shieldpy.automata.product import product
from shieldpy.automata.game import SafetyGame
from shieldpy.smt.encoding import encode_safetygame


# @pytest.mark.skip(reason="Not implemented")
def test_shield(simple_nfa, simple_spec):
    nfa1,_,_ = simple_nfa
    safety_automaton = compile_spec(simple_spec)
    game = product(nfa1, safety_automaton)
    transition_func, constraints, states, alphabet = encode_safetygame(game)

    s = z3.Solver()
    s.add(constraints)
    assert s.check() == z3.sat
    m = s.model()
    for t in game.transitions:
        start = states[t.start.value - 1]
        symbol = alphabet[t.symbol.value - 1]
        end = states[t.end.value - 1]
        f = transition_func(start, symbol, end)
        yval = m.evaluate(f)
        assert yval

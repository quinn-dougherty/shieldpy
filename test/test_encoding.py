import pytest
import z3
from shieldpy.nfa import create_state_enum, create_alphabet_enum, Transition, NFA
from shieldpy.smt.encoding import encode_state_enum, encode_transitions


@pytest.mark.skip(reason="idk how to clear z3 declarations skipping for now")
def test_encode_state_enum():
    State = create_state_enum(2)
    state = encode_state_enum(State)
    s = z3.Solver()
    state_var = z3.Const("state", state)
    s.add(state_var == state.q0)
    assert s.check() == z3.sat


def test_encode_transitions(simple_state, simple_alphabet, simple_transitions):
    transition_func, constraints, states, alphabets = encode_transitions(
        simple_state, simple_alphabet, simple_transitions
    )
    s = z3.Solver()
    s.add(constraints)
    assert s.check() == z3.sat
    m = s.model()
    for t in simple_transitions:
        f = transition_func(
            states[t.start.value - 1],
            alphabets[t.symbol.value - 1],
            states[t.end.value - 1],
            True,
        )
        assert m[f] == getattr(simple_state, t.end.name)


def test_z3_function_sanity():
    """ "just to learn z3"""
    s = z3.Solver()
    f = z3.Function("f", z3.IntSort(), z3.IntSort())
    x = z3.Int("x")
    s.add(f(x) == x)
    assert s.check() == z3.sat
    m = s.model()
    x_val = m.evaluate(x)
    y = f(x_val)
    y_val = m.evaluate(y)
    assert y_val == x_val


def test_z3_function_identity():
    """just to learn z3"""
    s = z3.Solver()
    f = z3.Function("f", z3.IntSort(), z3.IntSort())
    x = z3.Int("x")
    s.add(z3.ForAll(x, f(x) == x))
    assert s.check() == z3.sat
    m = s.model()

    # test on literal consts
    for i in range(-5, 6):
        assert m.evaluate(f(i)) == i

    # test on symbolic variables
    y = m.evaluate(f(x))
    assert z3.is_expr(y) and y.decl().name() == x.decl().name()

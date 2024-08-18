import pytest
import z3
from shieldpy.nfa import create_state_enum, create_alphabet_enum, Transition, NFA
from shieldpy.smt.encoding import encode_state_enum, encode_transitions


def test_encode_state_enum():
    State = create_state_enum(2)
    state = encode_state_enum(State)
    s = z3.Solver()
    state_var = z3.Const("state", state)
    s.add(state_var == state.q0)
    assert s.check() == z3.sat


# @pytest.mark.skip(reason="Not implemented")
def test_encode_transitions(simple_state, simple_alphabet, simple_transitions):
    transition_func, constraints = encode_transitions(
        simple_state, simple_alphabet, simple_transitions
    )
    s = z3.Solver()
    s.add(constraints)
    assert s.check() == z3.sat
    m = s.model()
    for t in simple_transitions:
        assert m[
            transition_func(
                getattr(simple_state, t.start.name),
                getattr(simple_alphabet, t.symbol.name),
                True,
            )
        ] == getattr(simple_state, t.end.name)


@pytest.mark.skip(reason="Not implemented")
def test_z3_function_sanity():
    s = z3.Solver()
    f = z3.Function("f", z3.IntSort(), z3.IntSort())
    x = z3.Int("x")
    s.add(f(x) == x)
    assert s.check() == z3.sat
    m = s.model()
    y = f(x)
    assert m[y] == x

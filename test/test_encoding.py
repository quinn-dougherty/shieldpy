import pytest
import z3
from shieldpy.nfa import create_state_enum
from shieldpy.smt.encoding import encode_state_enum, encode_transitions


@pytest.mark.skip(reason="idk how to clear z3 declarations skipping for now")
def test_encode_state_enum():
    State = create_state_enum(2)
    state = encode_state_enum(State)
    s = z3.Solver()
    state_var = z3.Const("state", state)
    s.add(state_var == state.q0)
    assert s.check() == z3.sat


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


def test_z3_enum_function():
    """just to learn z3"""
    # Define two enumeration types
    ColorType = z3.Datatype("ColorType")
    ColorType.declare("Red")
    ColorType.declare("Green")
    ColorType.declare("Blue")
    ColorType = ColorType.create()

    ShapeType = z3.Datatype("ShapeType")
    ShapeType.declare("Circle")
    ShapeType.declare("Square")
    ShapeType = ShapeType.create()

    # Define a function from ColorType and ShapeType to Bool
    property_func = z3.Function("property_func", ColorType, ShapeType, z3.BoolSort())

    s = z3.Solver()

    # Add some rules for the function
    s.add(property_func(ColorType.Red, ShapeType.Circle))
    s.add(property_func(ColorType.Green, ShapeType.Square))
    c = z3.Const("c", ColorType)
    s.add(
        z3.ForAll(
            [c],
            property_func(c, ShapeType.Square),
        )
    )
    s.add(z3.Not(property_func(ColorType.Blue, ShapeType.Circle)))

    assert s.check() == z3.sat
    m = s.model()

    # Test specific function calls
    assert m.evaluate(property_func(ColorType.Red, ShapeType.Circle))
    assert m.evaluate(property_func(ColorType.Green, ShapeType.Square))
    assert m.evaluate(property_func(ColorType.Blue, ShapeType.Square))
    assert not m.evaluate(property_func(ColorType.Blue, ShapeType.Circle))

    # Test the universal quantifier
    for color in [ColorType.Red, ColorType.Green, ColorType.Blue]:
        assert m.evaluate(property_func(color, ShapeType.Square))


def test_encode_transitions(simple_state, simple_alphabet, simple_transitions):
    transition_func, constraints, states, alphabets = encode_transitions(
        simple_state, simple_alphabet, simple_transitions
    )
    s = z3.Solver()
    s.add(constraints)
    assert s.check() == z3.sat
    m = s.model()
    for t in simple_transitions:
        start = states[t.start.value - 1]
        symbol = alphabets[t.symbol.value - 1]
        end = states[t.end.value - 1]
        f = transition_func(
            start,
            symbol,
            end,
        )
        yval = m.evaluate(f)
        assert yval

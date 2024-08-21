from shieldpy.logic import syntax


def test_atom_syntax():
    a = syntax.atom("p")
    assert syntax.to_repr(a) == "p"
    assert syntax.get_atoms(a) == {"p"}


def test_true_constant_syntax():
    t = syntax.true()
    assert syntax.to_repr(t) == "true"
    assert syntax.get_atoms(t) == set()


def test_false_syntax():
    f = syntax.false()
    assert syntax.to_repr(f) == "!(true)"
    assert syntax.get_atoms(f) == set()


def test_not_syntax():
    not_p = syntax.not_(syntax.atom("p"))
    assert syntax.to_repr(not_p) == "!(p)"
    assert syntax.get_atoms(not_p) == {"p"}


def test_and_syntax():
    p_and_q = syntax.and_(syntax.atom("p"), syntax.atom("q"))
    assert syntax.to_repr(p_and_q) == "(p & q)"
    assert syntax.get_atoms(p_and_q) == {"p", "q"}


def test_or_syntax():
    p_or_q = syntax.or_(syntax.atom("p"), syntax.atom("q"))
    assert syntax.to_repr(p_or_q) == "(p | q)"
    assert syntax.get_atoms(p_or_q) == {"p", "q"}


def test_implies_syntax():
    p_implies_q = syntax.implies(syntax.atom("p"), syntax.atom("q"))
    assert syntax.to_repr(p_implies_q) == "(p -> q)"
    assert syntax.get_atoms(p_implies_q) == {"p", "q"}


def test_until_syntax():
    p_until_q = syntax.until(syntax.atom("p"), syntax.atom("q"))
    assert syntax.to_repr(p_until_q) == "(p U q)"
    assert syntax.get_atoms(p_until_q) == {"p", "q"}


def test_eventually_syntax():
    eventually_p = syntax.eventually(syntax.atom("p"))
    assert syntax.to_repr(eventually_p) == "(true U p)"
    assert syntax.pretty_print(eventually_p) == "F(p)"
    assert syntax.get_atoms(eventually_p) == {"p"}


def test_always_syntax():
    always_p = syntax.always(syntax.atom("p"))
    # assert syntax.to_repr(always_p) == "(!((true U (!(p)))))"
    assert syntax.pretty_print(always_p) == "G(p)"
    assert syntax.get_atoms(always_p) == {"p"}


def test_next_syntax():
    next_p = syntax.next_(syntax.atom("p"))
    # assert syntax.to_repr(next_p) == "((!(true)) U p)"
    assert syntax.pretty_print(next_p) == "X(p)"
    assert syntax.get_atoms(next_p) == {"p"}


def test_safety_property_syntax():
    safety_property = syntax.always(
        syntax.implies(syntax.atom("request"), syntax.next_(syntax.atom("grant")))
    )
    assert syntax.pretty_print(safety_property) == "G((request -> X(grant)))"
    assert syntax.get_atoms(safety_property) == {"request", "grant"}


def test_invariance_syntax():
    invariance = syntax.always(syntax.atom("safe"))
    assert syntax.pretty_print(invariance) == "G(safe)"
    assert syntax.get_atoms(invariance) == {"safe"}


def test_liveness_syntax():
    liveness = syntax.eventually(syntax.atom("goal"))
    assert syntax.pretty_print(liveness) == "F(goal)"
    assert syntax.get_atoms(liveness) == {"goal"}


def test_response_syntax():
    response = syntax.always(
        syntax.implies(
            syntax.atom("trigger"), syntax.eventually(syntax.atom("response"))
        )
    )
    assert syntax.pretty_print(response) == "G((trigger -> F(response)))"
    assert syntax.get_atoms(response) == {"trigger", "response"}


def test_complex_formula_syntax():
    complex_formula = syntax.and_(
        syntax.always(
            syntax.implies(syntax.atom("p"), syntax.eventually(syntax.atom("q")))
        ),
        syntax.until(syntax.not_(syntax.atom("r")), syntax.atom("s")),
    )
    # expected_string = "(((!((true U (!(((p -> (true U q))))))) & ((!(r)) U s)))"
    # assert syntax.to_repr(complex_formula) == expected_string
    # assert syntax.pretty_print(complex_formula) == "(G((p -> F(q))) & ((!(r)) U s))"
    assert syntax.get_atoms(complex_formula) == {"p", "q", "r", "s"}


def test_nested_temporal_operators_syntax():
    nested = syntax.always(syntax.eventually(syntax.always(syntax.atom("p"))))
    assert syntax.pretty_print(nested) == "G(F(G(p)))"
    assert syntax.get_atoms(nested) == {"p"}

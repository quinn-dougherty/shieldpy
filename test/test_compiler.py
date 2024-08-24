import pytest
from enum import Enum
from shieldpy.automata.nondeterministic_finite import NFA
from shieldpy.logic.syntax import (
    Atom,
    TrueConstant,
    UnaryOp,
    BinaryOp,
    Operator,
)
from shieldpy.compiler import compile_spec
from shieldpy.automata.visualize import visualize_nfa

def test_atom():
    formula = Atom("p")
    nfa = compile_spec(formula)

    assert isinstance(nfa, NFA), "compile_spec should return an NFA instance"
    assert len(nfa.states) == 2, "Atom NFA should have 2 states"
    assert len(nfa.alphabet) == 1, "Atom NFA should have 1 alphabet symbol"
    assert len(nfa.transitions) == 1, "Atom NFA should have 1 transition"
    assert len(nfa.accept) == 1, "Atom NFA should have 1 accept state"


def test_true_constant():
    formula = TrueConstant()
    nfa = compile_spec(formula)

    assert isinstance(nfa, NFA), "compile_spec should return an NFA instance"
    assert len(nfa.states) == 2, "TrueConstant NFA should have 2 states"
    assert len(nfa.alphabet) == 1, "TrueConstant NFA should have 1 alphabet symbol"
    assert len(nfa.transitions) == 1, "TrueConstant NFA should have 1 transition"
    assert len(nfa.accept) == 1, "TrueConstant NFA should have 1 accept state"


def test_not_operator():
    formula = UnaryOp(Operator.NOT, Atom("p"))
    nfa = compile_spec(formula)

    assert isinstance(nfa, NFA), "compile_spec should return an NFA instance"
    assert len(nfa.states) == 3, "NOT operator NFA should have 3 states"
    assert len(nfa.alphabet) == 2, "NOT operator NFA should have 2 alphabet symbols"
    assert len(nfa.transitions) == 2, "NOT operator NFA should have 2 transitions"
    assert len(nfa.accept) == 1, "NOT operator NFA should have 1 accept state"


def test_and_operator():
    formula = BinaryOp(Operator.AND, Atom("p"), Atom("q"))
    nfa = compile_spec(formula)

    # FIXME Debugging
    visualize_nfa(nfa)

    assert isinstance(nfa, NFA), "compile_spec should return an NFA instance"
    assert len(nfa.states) == 4, "AND operator NFA should have 4 states"
    assert len(nfa.alphabet) == 3, "AND operator NFA should have 3 alphabet symbols"
    assert len(nfa.transitions) == 3, "AND operator NFA should have 3 transitions"
    assert len(nfa.accept) == 1, "AND operator NFA should have 1 accept state"


def test_or_operator():
    formula = BinaryOp(Operator.OR, Atom("p"), Atom("q"))
    nfa = compile_spec(formula)

    assert isinstance(nfa, NFA), "compile_spec should return an NFA instance"
    assert len(nfa.states) == 2, "OR operator NFA should have 2 states"
    assert len(nfa.alphabet) == 2, "OR operator NFA should have 2 alphabet symbols"
    assert len(nfa.transitions) == 2, "OR operator NFA should have 2 transitions"
    assert len(nfa.accept) == 1, "OR operator NFA should have 1 accept state"


def test_until_operator():
    formula = BinaryOp(Operator.UNTIL, Atom("p"), Atom("q"))
    nfa = compile_spec(formula)

    assert isinstance(nfa, NFA), "compile_spec should return an NFA instance"
    assert len(nfa.states) == 3, "UNTIL operator NFA should have 3 states"
    assert len(nfa.alphabet) == 3, "UNTIL operator NFA should have 3 alphabet symbols"
    assert len(nfa.transitions) == 3, "UNTIL operator NFA should have 3 transitions"
    assert len(nfa.accept) == 1, "UNTIL operator NFA should have 1 accept state"


def test_complex_formula():
    formula = BinaryOp(
        Operator.AND,
        UnaryOp(Operator.NOT, Atom("p")),
        BinaryOp(Operator.UNTIL, Atom("q"), Atom("r")),
    )
    nfa = compile_spec(formula)

    assert isinstance(nfa, NFA), "compile_spec should return an NFA instance"
    assert len(nfa.states) > 4, "Complex formula NFA should have more than 4 states"
    assert (
        len(nfa.alphabet) > 3
    ), "Complex formula NFA should have more than 3 alphabet symbols"
    assert (
        len(nfa.transitions) > 4
    ), "Complex formula NFA should have more than 4 transitions"
    assert len(nfa.accept) == 1, "Complex formula NFA should have 1 accept state"


def test_accepts_atom():
    Alphabet = Enum("Alphabet", ["p", "q"])
    formula = Atom("p")
    nfa = compile_spec(formula)

    assert nfa.accepts([Alphabet.p]), "NFA for Atom('p') should accept [p]"
    assert not nfa.accepts([Alphabet.q]), "NFA for Atom('p') should not accept [q]"
    assert not nfa.accepts([]), "NFA for Atom('p') should not accept empty word"


def test_accepts_true_constant():
    Alphabet = Enum("Alphabet", ["TRUE", "p"])
    formula = TrueConstant()
    nfa = compile_spec(formula)

    assert nfa.accepts([Alphabet.TRUE]), "NFA for TrueConstant should accept [TRUE]"
    assert not nfa.accepts([Alphabet.p]), "NFA for TrueConstant should not accept [p]"
    assert not nfa.accepts([]), "NFA for TrueConstant should not accept empty word"


def test_accepts_not():
    Alphabet = Enum("Alphabet", ["p", "q", "r", "NOT"])
    formula = UnaryOp(Operator.NOT, Atom("p"))
    nfa = compile_spec(formula)

    assert nfa.accepts(
        [Alphabet.q, Alphabet.NOT]
    ), "NFA for NOT p should accept [q, NOT]"
    assert nfa.accepts(
        [Alphabet.r, Alphabet.NOT]
    ), "NFA for NOT p should accept [r, NOT]"
    assert not nfa.accepts(
        [Alphabet.p, Alphabet.NOT]
    ), "NFA for NOT p should not accept [p, NOT]"
    assert not nfa.accepts(
        [Alphabet.NOT]
    ), "NFA for NOT p should not accept [NOT] alone"
    assert not nfa.accepts([Alphabet.p]), "NFA for NOT p should not accept [p]"


def test_accepts_and():
    Alphabet = Enum("Alphabet", ["p", "q", "AND"])
    formula = BinaryOp(Operator.AND, Atom("p"), Atom("q"))
    nfa = compile_spec(formula)

    assert nfa.accepts(
        [Alphabet.p, Alphabet.q, Alphabet.AND]
    ), "NFA for p AND q should accept [p, q, AND]"
    assert not nfa.accepts(
        [Alphabet.p, Alphabet.AND]
    ), "NFA for p AND q should not accept [p, AND]"
    assert not nfa.accepts(
        [Alphabet.q, Alphabet.AND]
    ), "NFA for p AND q should not accept [q, AND]"
    assert not nfa.accepts(
        [Alphabet.p, Alphabet.q]
    ), "NFA for p AND q should not accept [p, q] without AND"


def test_accepts_or():
    Alphabet = Enum("Alphabet", ["p", "q", "r"])
    formula = BinaryOp(Operator.OR, Atom("p"), Atom("q"))
    nfa = compile_spec(formula)

    assert nfa.accepts([Alphabet.p]), "NFA for p OR q should accept [p]"
    assert nfa.accepts([Alphabet.q]), "NFA for p OR q should accept [q]"
    assert not nfa.accepts([Alphabet.r]), "NFA for p OR q should not accept [r]"
    assert not nfa.accepts([]), "NFA for p OR q should not accept empty word"


def test_accepts_until():
    Alphabet = Enum("Alphabet", ["p", "q", "UNTIL"])
    formula = BinaryOp(Operator.UNTIL, Atom("p"), Atom("q"))
    nfa = compile_spec(formula)

    assert nfa.accepts([Alphabet.q]), "NFA for p UNTIL q should accept [q]"
    assert nfa.accepts(
        [Alphabet.p, Alphabet.UNTIL, Alphabet.q]
    ), "NFA for p UNTIL q should accept [p, UNTIL, q]"
    assert nfa.accepts(
        [Alphabet.p, Alphabet.UNTIL, Alphabet.p, Alphabet.UNTIL, Alphabet.q]
    ), "NFA for p UNTIL q should accept [p, UNTIL, p, UNTIL, q]"
    assert not nfa.accepts(
        [Alphabet.p]
    ), "NFA for p UNTIL q should not accept [p] alone"
    assert not nfa.accepts(
        [Alphabet.p, Alphabet.UNTIL, Alphabet.p]
    ), "NFA for p UNTIL q should not accept [p, UNTIL, p]"


def test_accepts_complex_formula():
    Alphabet = Enum("Alphabet", ["p", "q", "r", "NOT", "UNTIL", "AND"])
    # Formula: (NOT p) AND (q UNTIL r)
    formula = BinaryOp(
        Operator.AND,
        UnaryOp(Operator.NOT, Atom("p")),
        BinaryOp(Operator.UNTIL, Atom("q"), Atom("r")),
    )
    nfa = compile_spec(formula)

    assert nfa.accepts(
        [Alphabet.q, Alphabet.NOT, Alphabet.UNTIL, Alphabet.r, Alphabet.AND]
    ), "NFA for (NOT p) AND (q UNTIL r) should accept [q, NOT, UNTIL, r, AND]"
    assert nfa.accepts(
        [
            Alphabet.q,
            Alphabet.UNTIL,
            Alphabet.q,
            Alphabet.NOT,
            Alphabet.UNTIL,
            Alphabet.r,
            Alphabet.AND,
        ]
    ), "NFA for (NOT p) AND (q UNTIL r) should accept [q, UNTIL, q, NOT, UNTIL, r, AND]"
    assert not nfa.accepts(
        [Alphabet.p, Alphabet.NOT, Alphabet.UNTIL, Alphabet.r, Alphabet.AND]
    ), "NFA for (NOT p) AND (q UNTIL r) should not accept [p, NOT, UNTIL, r, AND]"
    assert not nfa.accepts(
        [Alphabet.q, Alphabet.NOT, Alphabet.UNTIL, Alphabet.q, Alphabet.AND]
    ), "NFA for (NOT p) AND (q UNTIL r) should not accept [q, NOT, UNTIL, q, AND]"
    assert not nfa.accepts(
        [Alphabet.p, Alphabet.q, Alphabet.r]
    ), "NFA for (NOT p) AND (q UNTIL r) should not accept [p, q, r]"


def test_unsupported_unary_operator():
    class UnsupportedOp(Enum):
        UNKNOWN = "UNKNOWN"

    formula = UnaryOp(UnsupportedOp.UNKNOWN, Atom("p"))
    with pytest.raises(ValueError, match="Unsupported unary operator"):
        compile_spec(formula)


def test_unsupported_binary_operator():
    class UnsupportedOp(Enum):
        UNKNOWN = "UNKNOWN"

    formula = BinaryOp(UnsupportedOp.UNKNOWN, Atom("p"), Atom("q"))
    with pytest.raises(ValueError, match="Unsupported binary operator"):
        compile_spec(formula)

from shieldpy.automata.nondeterministic_finite import NFA
from shieldpy.logic.syntax import LTLFormula
from shieldpy.compiler import compile_spec


def product(nfa1: NFA, nfa2: NFA) -> NFA:
    """
    Computes the product of two NFAs.

    The product of two NFAs is another NFA that accepts the intersection of the
    languages of the two NFAs.
    """
    pass


def create_game(environment: NFA, spec: LTLFormula) -> NFA:
    """
    Creates a game between the environment and the specification.

    The game is represented as an NFA.
    """
    nfa2 = compile_spec(spec)
    return product(environment, nfa2)

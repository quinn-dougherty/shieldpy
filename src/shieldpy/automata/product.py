from shieldpy.automata.nondeterministic_finite import NFA
from shieldpy.logic.syntax import LTLFormula
from shieldpy.compiler import compile_spec
from shieldpy.automata.game import SafetyGame
from aenum import IntEnum

def product(nfa1: NFA, nfa2: NFA) -> SafetyGame:
    """
    Computes the product of two NFAs.

    The product of two NFAs is another NFA that accepts the intersection of the
    languages of the two NFAs.
    """
    states = {(s1, s2) for s1 in nfa1.states for s2 in nfa2.states}
    alphabets = nfa1.alphabet.union(nfa2.alphabet)
    initial_states = {(nfa1.start, nfa2.start)}
    safe_states = {(s1, s2) for s1 in nfa1.accept for s2 in nfa2.accept}

    transitions = {} # TODO

    return prune(SafetyGame(states, transitions, initial_states, safe_states, alphabets))


def prune(nfa: NFA) -> NFA:
    """
    Prunes the NFA by removing unreachable states.
    """
    pass

def create_game(environment: NFA, spec: LTLFormula) -> NFA:
    """
    Creates a game between the environment and the specification.

    The game is represented as an NFA.
    """
    nfa2 = compile_spec(spec)
    return product(environment, nfa2)

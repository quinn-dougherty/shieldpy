from shieldpy.automata.nondeterministic_finite import NFA, Transition
from shieldpy.logic.syntax import LTLFormula
from shieldpy.compiler import compile_spec
from shieldpy.automata.game import SafetyGame


def product(nfa1: NFA, nfa2: NFA) -> SafetyGame:
    """
    Computes the product of two NFAs.

    The product of two NFAs is another NFA that accepts the intersection of the
    languages of the two NFAs.
    """
    states = frozenset((s1, s2) for s1 in nfa1.states for s2 in nfa2.states)
    # TODO The alphabet should be be the intersection so they should be using the same Enum?
    alphabets = nfa1.alphabet.intersect(nfa2.alphabet)
    initial_states = (nfa1.start, nfa2.start)
    safe_states = frozenset((s1, s2) for s1 in nfa1.accept for s2 in nfa2.accept)

    transitions = []
    for t1 in nfa1.transitions:
        for t2 in nfa2.transitions:
            if t1.symbol == t2.symbol:
                transitions.append(
                    Transition(
                        start=(t1.start, t2.start),
                        symbol=t1.symbol,
                        end=(t1.end, t2.end),
                    )
                )

    return prune(
        SafetyGame(states, transitions, initial_states, safe_states, alphabets)
    )


def prune(nfa: SafetyGame) -> SafetyGame:
    """
    Prunes the product NFA by removing unreachable states.
    """
    # TODO Do a search and mark reachable states
    # TODO not sure if we need this right away?
    return nfa


def create_game(environment: NFA, spec: LTLFormula) -> NFA:
    """
    Creates a game between the environment and the specification.

    The game is represented as an NFA.
    """
    nfa2 = compile_spec(spec)
    return product(environment, nfa2)

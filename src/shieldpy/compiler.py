from enum import Enum
from shieldpy.automata.nondeterministic_finite import NFA, Transition
from shieldpy.logic.syntax import (
    LTLFormula,
    Atom,
    TrueConstant,
    UnaryOp,
    BinaryOp,
    Operator,
)


def compile_spec(formula: LTLFormula) -> NFA:
    """
    Compiles an LTL formula into an NFA.

    It's supposed to land in buchi automata, but we're gonna try to cheat
    """
    state_counter = 0
    alphabet = list()
    states = list()
    transitions_staging = set()
    accept_states = set()

    def new_state() -> str:
        nonlocal states, state_counter
        state = f"q{state_counter}"
        state_counter += 1
        states.append(state)
        return state

    def process_formula(f: LTLFormula, start: str, end: str):
        nonlocal alphabet, transitions, accept_states

        match f:
            case Atom(name):
                alphabet.append(name)
                transitions_staging.add((start, name, end))

            case TrueConstant():
                true_symbol = "TRUE"
                alphabet.append(true_symbol)
                transitions_staging.add((start, true_symbol, end))

            case UnaryOp(op=Operator.NOT, sub=sub):
                mid = new_state()
                process_formula(sub, start, mid)
                not_symbol = "NOT"
                alphabet.append(not_symbol)
                transitions_staging.add((mid, not_symbol, end))

            case UnaryOp():
                raise ValueError(f"Unsupported unary operator: {f.op}")

            case BinaryOp(op=Operator.AND, left=left, right=right):
                mid1, mid2 = new_state(), new_state()
                process_formula(left, start, mid1)
                process_formula(right, mid1, mid2)
                and_symbol = "AND"
                alphabet.append(and_symbol)
                transitions_staging.add((mid2, and_symbol, end))

            case BinaryOp(op=Operator.OR, left=left, right=right):
                process_formula(left, start, end)
                process_formula(right, start, end)

            case BinaryOp(op=Operator.UNTIL, left=left, right=right):
                mid = new_state()
                process_formula(right, start, end)
                process_formula(left, start, mid)
                until_symbol = "UNTIL"
                alphabet.append(until_symbol)
                transitions_staging.add((mid, until_symbol, start))

            case BinaryOp():
                raise ValueError(f"Unsupported binary operator: {f.op}")

    start_state = new_state()
    final_state = new_state()

    process_formula(formula, start_state, final_state)

    States = Enum("States", states)
    Alphabet = Enum("Alphabet", alphabet)
    transitions = {
        Transition(
            getattr(States, s), getattr(Alphabet, letter), getattr(States, output)
        )
        for s, letter, output in transitions_staging
    }
    start_state = getattr(States, start_state)
    final_state = getattr(States, final_state)
    accept_states.add(final_state)
    return NFA(
        states=States,
        transitions=frozenset(transitions),
        start=start_state,
        accept=frozenset(accept_states),
        alphabet=Alphabet,
    )

from shieldpy.logic.syntax import (
    Atom,
    BinaryOp,
    Operator,
)
from shieldpy.compiler import compile_spec


def main() -> str:
    # Example usage
    formula = BinaryOp(Operator.UNTIL, Atom("p"), Atom("q"))

    nfa = compile_spec(formula)
    print(f"States: {nfa.states}")
    print(f"Transitions: {nfa.transitions}")
    print(f"Start state: {nfa.start}")
    print(f"Accept states: {nfa.accept}")
    print(f"Alphabet: {nfa.alphabet}")

    return "Hello from shieldpy!"

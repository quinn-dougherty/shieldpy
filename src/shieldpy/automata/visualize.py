from shieldpy.automata.nondeterministic_finite import NFA, Transition
from visual_automata.fa.nfa import VisualNFA

def visualize_nfa(nfa: NFA):
    """Visualize the NFA using an automata visualization library.
    """

    nfa = VisualNFA(
        states={s.name for s in nfa.states},
        # TODO maybe need merge operator on all match t.start.name for the format they have?
        transitions= {
            t.start.name: {
                t.symbol.name: {t.end.name}
            } for t in nfa.transitions
        }, # TODO
        initial_state=nfa.start.name,
        final_states={s for s in nfa.accept},
        input_symbols={a.name for a in nfa.alphabet}
    )
    nfa.show_diagram(view=True)

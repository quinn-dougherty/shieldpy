from typing import NewType
from shieldpy.automata.nondeterministic_finite import NFA, Transition
from enum import Enum
from shieldpy.logic.syntax import and_, always, atom, next_, implies

# Water Tank Example from Figure 5 but simplified

## PROMPT (TODO prompt is sparse here probably include more details in the prompt)
## https://arxiv.org/pdf/2306.12672 See Figure 13 for prompting example for world model generation.
## They use a probabalistic program but the same applies here.
## ---------- START ------------

# We define a water tank system with a switch that can be either open or closed

WaterTankState = Enum("WaterTankState", [f"q_{i}" for i in range(99)])

WaterTankAlphabet = Enum("WaterTankAlphabet", ["OPEN", "CLOSE"])

transitions = set()

# Transition 1 step forward
for i in range(98):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        WaterTankAlphabet.OPEN,
        getattr(WaterTankState, f"q_{i+1}")
    ))

# Transition 1 step backward
for i in range(1, 99):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        WaterTankAlphabet.CLOSE,
        getattr(WaterTankState, f"q_{i-1}")
    ))

watertank_nfa = NFA(
    states = WaterTankState,
    transitions = frozenset(transitions),
    start = WaterTankState.q_0,
    accept = frozenset([e for e in WaterTankState]),
    alphabet= WaterTankAlphabet
)

# Section 4, Example 1, Page 7 contains the LTL specification for the water tank system
# TODO don't we need the same alphabets otherwise we won't have an intersection when constructing the product automaton?

open_ = atom("OPEN")
close = atom("CLOSE")

validStates = [atom(x.name) for x in WaterTankState.members] # [q_0, q_1, ..., q_99]

neverEmpty = always(not_(atom("q_0"))

openThenClosed = and_(open_, next_(close))

# If open and then we close, the tank should be continued to be closed for 2 more steps
openThenClosedImpliesClosedTwoSteps = always(
    implies(
        openThenClosed,
        and_(
            next_(next_(close)),
            next_(next_(next_(close)))
        )
    )
)

# The interesting part to our research is that copilot started generating the next two formulas automatically
closedThenOpen = and_(close, next_(open_))

# If closed and then we open, the tank should be continued to be open for 2 more steps
closedThenOpenImpliesOpenTwoSteps = always(
    implies(
        closedThenOpen,
        and_(
            next_(next_(open_)),
            next_(next_(next_(open_)))
        )
    )
)

spec = and_(always(levelOver0)
                      , and_(levelUnder100
                            , and_(openThenClosedImpliesClosedTwoSteps
                                    , closedThenOpenImpliesOpenTwoSteps)))

# Now define a world model NFA for [INSERT ] the above is completely unrelated

from typing import NewType
from shieldpy.automata.nondeterministic_finite import NFA, Transition
from enum import Enum
from shieldpy.logic.syntax import and_, always, atom, next_, implies

# Water Tank Example from Figure 5

## PROMPT (TODO prompt is sparse here probably include more details in the prompt)
## https://arxiv.org/pdf/2306.12672 See Figure 13 for prompting example for world model generation.
## They use a probabalistic program but the same applies here.
## ---------- START ------------

# We define a water tank system with a switch that can be either open or closed

Level = NewType('Level', int)
minLevel = Level(0)
maxLevel = Level(100)

WaterTankState = Enum("WaterTankState", [f"q_{i}" for i in range(99)])

WaterTankAlphabet = Enum("WaterTankAlphabet", [f"(open, {i} <= level < {i+1})" for i in range(1, 99)] + [f"(close, {i} <= level < {i + 1})" for i in range(99)])

transitions = set()

# Transition back to self for open and close shown in diagram as a *
for i in range(99):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(open, {i} <= level < {i+1})"),
        getattr(WaterTankState, f"q_{i}")
    ))
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(close, {i} <= level < {i+1})"),
        getattr(WaterTankState, f"q_{i}")
    ))

# Transition 1 step forward
for i in range(98):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(open, {i+1} <= level < {i+2})"),
        getattr(WaterTankState, f"q_{i+1}")
    ))

# Transition 2 steps forward
for i in range(97):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(close, {i+1} <= level < {i+3})"),
        getattr(WaterTankState, f"q_{i+2}")
    ))

# TODO are there n steps forward transitions?
# The diagram doesn't make it explicit and we are uncertain so assuming no for now.
# Additionally assuming there is only 1 transition backwards

# Transition 1 step backward
for i in range(1, 99):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(close, {i-1} <= level < {i})"),
        getattr(WaterTankState, f"q_{i-1}")
    ))

watertank_nfa = NFA(
    states = WaterTankState,
    transitions = frozenset(transitions),
    start = WaterTankState.q_0,
    accept = frozenset([e for e in WaterTankState]),
    alphabet= WaterTankAlphabet
)

# TODO create LTL spec


# Section 4, Example 1, Page 7 contains the LTL specification for the water tank system
# TODO don't we need the same alphabets otherwise we won't have an intersection when constructing the product automaton?

open_ = atom("open")
close = atom("close")
levelUnder100 = atom("level < 100")
levelOver0 = atom("level > 0")

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

from typing import NewType
from shieldpy.automata.nondeterministic_finite import NFA, Transition
from enum import Enum

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

# Do I need the * self loop?
WaterTankAlphabet = Enum("WaterTankAlphabet", [f"(open, {i} <= level < {i+1})" for i in range(1, 99)] + [f"(close, {i} <= level < {i + 1})" for i in range(99)])


# TODO going to make transitions programatically
transitions = set()

# Transition 1 step forward
for i in range(98):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(open, {i} <= level < {i+1})"),
        getattr(WaterTankState, f"q_{i+1}")
    ))

# Transition 2 steps forward
for i in range(97):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(close, {i} <= level < {i+2})"),
        getattr(WaterTankState, f"q_{i+2}")
    ))

# TODO are there n steps forward transitions?

# Transition 1 step backward

for i in range(1, 99):
    transitions.add(Transition(
        getattr(WaterTankState, f"q_{i}"),
        getattr(WaterTankAlphabet, f"(close, {i-1} <= level < {i})"),
        getattr(WaterTankState, f"q_{i-1}")
    ))

# TODO diagram doesn't show n > 1 steps backward but double check

# TODO * loops

watertank_nfa = NFA(
    states = WaterTankState,
    transitions = frozenset(transitions),
    start = WaterTankState.q_0,
    accept = frozenset([e for e in WaterTankState]),
    alphabet= WaterTankAlphabet
)

# TODO create LTL spec

# Now define a world model NFA for [INSERT ] the above is completely unrelated

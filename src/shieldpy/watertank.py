from typing import NewType
from shieldpy.automata.nondeterministic_finite import NFA, Transition
from enum import Enum

# Water Tank Example from Figure 4
# TODO do we want figure 4 or 5? Pretty sure figure 4
# TODO move this to something like examples/

## PROMPT (TODO prompt is sparse here probably include more details in the prompt)
## https://arxiv.org/pdf/2306.12672 See Figure 13 for prompting example for world model generation.
## They use a probabalistic program but the same applies here.
## ---------- START ------------

# We define a water tank system with a switch that can be either open or closed



Level = NewType('Level', int)
minLevel = Level(0)
maxLevel = Level(100)


WaterTankState = Enum("WaterTankState", ["q_0", "q_b", "q_c", "q_d", "q_e", "q_f"])

# An "Ok level" is when 1 <= Level <= 99
WaterTankAlphabet = Enum("WaterTankAlphabet", ["CLOSE_AND_OK_LEVEL", "OPEN_AND_OK_LEVEL"])

# TODO rest of transition
transitions = {
    Transition(
        WaterTankState.q_0,
        WaterTankAlphabet.CLOSE_AND_OK_LEVEL,
        WaterTankState.q_0
    )
}

watertank_nfa = NFA(
    states = WaterTankState,
    transitions = transitions,
    start = Switch.CLOSE,
    accept = WaterTankState,
    alphabet= WaterTankAlphabet
)

# Now define a world model NFA for [INSERT ]

from typing import NewType
from nfa import NFA, Transition
from dataclasses import dataclass
from enum import Enum

# Water Tank Example from Figure 4
# TODO do we want figure 4 or 5?
# TODO move this to something like examples/

Switch = Enum('Switch', ['OPEN', 'CLOSE'])

Level = NewType('Level', int)
minLevel = Level(0)
maxLevel = Level(100)


WaterTankState = Enum("WaterTankState", ["q_0", "q_b", "q_c", "q_d", "q_e", "q_f"])

# An "Ok level" is when 1 <= Level <= 99
WaterTankAlphabet = Enum("WaterTankAlphabet", ["closeAndOkLevel", "openAndOkLevel"])

# TODO rest of transition
transitions = {
    Transition(WaterTankState.q_0, WaterTankAlphabet.closeAndOkLevel, WaterTankState.q_0)
}

# TODO transitions, add levels, accept, alphabet
example = NFA(states = WaterTankState, transitions = transitions, start = Switch.CLOSE, accept = WaterTankState, alphabet= WaterTankAlphabet)


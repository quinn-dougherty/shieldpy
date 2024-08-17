import nfa
from typing import NewType

# Water Tank Example from Figure 4
# TODO do we want figure 4 or 5?
# TODO move this to something like examples/

Switch = Enum('Switch', ['OPEN', 'CLOSE'])

Level = NewType('Level', int) # Would be cool if I can bound this between 0 and 100
minLevel = Level(0)
maxLevel = Level(100)


WaterTankState = Enum("WaterTankState", ["q_0", "q_b", "q_c", "q_d", "q_e", "q_f"])

WaterTankAlphabet = pass # TODO

# TODO transitions, add levels, accept, alphabet
# Is accepting right?
example = NFA(states = [state.value for state in WaterTankState], transitions = {}, start = Switch.CLOSE, accept = [state.value for state in WaterTankState], alphabet= WaterTankAlphabet)

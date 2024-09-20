from ray.rllib.algorithms.ppo import PPOConfig
from ray.rllib.algorithms.algorithm import Algorithm
from shieldpy.environments.gymnasium.interface import DynNFAGymWrapper
from shieldpy.automata.dynamic_nondeterministic_finite import DynamicNFA
import gymnasium as gym
import os

# TODO LTL stuff?
def postPostedShield(algo: Algorithm, env):
    nfa = DynamicNFA()
    env = DynNFAGymWrapper(cartPoleEnv, nfa)

    done = False
    total_reward = 0
    observations = env.reset()
    while not done:
        # Learning agent proposes action
        action = algo.compute_single_action(observations)
        # Shield checks if action is safe
        # TODO maybe this is in step?
        observations, reward, done, info = env.step(action)
        total_reward += reward
        print("observations, reward, done, info",observations, reward, done, info)

def train(config, checkpoint: str):
    ppo = config.build()
    numTrainingLoop = 500
    for _ in range(numTrainingLoop):
        ppo.train()
    ppo.save(checkpoint)

# CartPole

cartPoleCheckpoint = "./cartPoleCheckpoint"
# Check if checkpoint exists
if os.path.isfile(cartPoleCheckpoint):
    config = PPOConfig().environment(env="CartPole-v1").training(train_batch_size=4000)
    algo = train(config, cartPoleCheckpoint)
else:
    algo = Algorithm.from_checkpoint(cartPoleCheckpoint)

env = gym.make("CartPole-v1")
postPostedShield(algo, env)

import gymnasium as gym
from shieldpy.environments.gymnasium.interface import DynNFAGymWrapper
from shieldpy.automata.dynamic_nondeterministic_finite import DynamicNFA


def main():
    env = gym.make("CartPole-v1")

    nfa = DynamicNFA()
    wrapped_env = DynNFAGymWrapper(env, nfa)
    # Set some accept state (e.g., when the pole is nearly upright)
    wrapped_env.set_accept_state((0.0, 0.0, 0.0, 0.0))  # Example state for CartPole

    obs, info = wrapped_env.reset()
    for _ in range(1000):
        action = (
            env.action_space.sample()
        )  # your agent here (this takes random actions)
        obs, reward, terminated, truncated, info = wrapped_env.step(action)
        if terminated or truncated:
            obs, info = wrapped_env.reset()

    wrapped_env.close()

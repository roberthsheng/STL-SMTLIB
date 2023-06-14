import compiler
import tseitin

def is_state_valuation(sigma):
    if not isinstance(sigma, dict):
        return False
    
    for key, value in sigma.items():
        if not isinstance(key, str) or not key[:-1].isalpha() or not key[-1].isdigit():
            return False
        
        if not isinstance(value, (int, float)):
            return False
            
    return True

def is_trajectory(trajectory):
    # check if trajectory is mapping from natural numbers to states
    if not isinstance(trajectory, dict):
        return False
    
    for key, value in trajectory.items():
        if not isinstance(key, int):
            return False
        
        if not is_state_valuation(value):
            return False
        
    return True

def satisfaction(trajectory, time, formula):
    if not is_trajectory(trajectory):
        return False
    state = trajectory[time]
    # replace variables at time t with their values
    smt = compiler.stl_to_smtlib(formula)
    for signal, real in state.items():
        smt = smt.replace(signal, str(real))
    
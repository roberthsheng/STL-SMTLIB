import re

# def ground_truth():

def is_possible(epsilon, deltas, signals, times):
    # assume epsilons[signal] is bound for signal
    # assume deltas[signal][time] is bound for signal at time
    clauses = []
    for signal in signals:
        clauses.append('(declare-const o' + str(signal) + ' Real)')
        clauses.append('(assert (and (<= (- ' + str(epsilon[signal]) + ') o' + str(signal) + ') (<= o' + str(signal) + ' ' + str(epsilon[signal]) + ')))')
        for time in times:
            clauses.append('(declare-const e' + str(signal) + str(time) + ' Real)')
            clauses.append('(assert (and (<= (- ' + str(deltas[signal][time]) + ') xe' + str(signal) + str(time) + ') (<= e' + str(signal) + str(time) + ' ' + str(deltas[signal][time]) + ')))')

    return clauses

def declare_helpers(formula):
    clauses = []
    # turn all instances of "pi" in formula into declared Bools, where i is a natural number
    pattern = r'pi\d+'
    matches = re.findall(pattern, formula)
    matches = list(set(matches))
    for pi in matches:
        clauses.append('(declare-const ' + pi + ' Bool)')

    # assumes original variables have already been declared
    clauses.append('(assert ' + formula + ')')
    return clauses


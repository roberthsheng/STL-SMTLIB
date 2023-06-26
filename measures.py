import re
import pandas

def is_possible(epsilon, deltas, signals, times, measurements):
    # assume epsilons[signal] is bound for signal
    # assume deltas[signal][time] is bound for signal at time
    clauses = []
    for signal in signals:
        clauses.append('(declare-const o' + str(signal) + ' Real)')
        clauses.append('(assert (and (<= (- ' + str(epsilon[signal]) + ') o' + str(signal) + ') (<= o' + str(signal) + ' ' + str(epsilon[signal]) + ')))')
        for time in times:
            clauses.append('(declare-const ' + str(signal) + str(time) + ' Real)')
            # Do we need to create bounds for xi? If so, #HACK
            # clauses.append('(assert (and (<= (- 9999999999999) ' + str(signal) + str(time) + ') (<= ' + str(signal) + str(time) + ' 9999999999999)))')

            clauses.append('(declare-const e' + str(signal) + str(time) + ' Real)')
            clauses.append('(assert (and (<= (- ' + str(deltas[signal][time]) + ') e' + str(signal) + str(time) + ') (<= e' + str(signal) + str(time) + ' ' + str(deltas[signal][time]) + ')))')
            clauses.append('(declare-const m' + str(signal) + str(time) + ' Real)')
            clauses.append('(assert (= m' + str(signal) + str(time) + ' ' + str(measurements[signal][time]) + '))')
            clauses.append('(assert (= (+ ' + str(signal) + str(time) + ' o' + str(signal) + ' e' + str(signal) + str(time) + ') m' + str(signal) + str(time) + '))')

    return clauses

def declare_helpers(formula):
    clauses = []
    # turn all instances of "pi" in formula into declared Bools, where i is a natural number
    helperPattern = r'p\d+'

    for pi in list(set(re.findall(helperPattern, formula))):
        clauses.append('(declare-const ' + pi + ' Bool)')

    # assumes original variables have already been declared
    clauses.append('(assert ' + formula + ')')
    return clauses

def measured(timeseries_csv):
    # csv with columns: signal, time, epsilon, delta, measurement
    df = pandas.read_csv(timeseries_csv)
    # # assert that epsilon is the same for all instances of a signal
    # if len(set(df['epsilon'])) != 1:
    #     raise ValueError('Epsilon must be the same for all instances of a signal')
    # map signal to epsilon
    epsilon = {signal: df['epsilon'][0] for signal in set(df['signal'])}
    # map signal to time to delta so that deltas[signal][time] = delta
    deltas = {signal: {} for signal in set(df['signal'])}
    for index, row in df.iterrows():
        deltas[row['signal']][row['time']] = row['delta']
    # map signal to time to measurement so that measurements[signal][time] = measurement
    measurements = {signal: {} for signal in set(df['signal'])}
    for index, row in df.iterrows():
        measurements[row['signal']][row['time']] = row['measurement']

    return epsilon, deltas, set(df['signal']), set(df['time']), measurements

def all_clauses(formula, file):
    epsilon, deltas, signals, times, measurements = measured('data/timeseries.csv')
    clauses = []
    clauses.append('(set-logic QF_LRA)')
    clauses.append('(set-option :print-success false)')
    clauses.extend(is_possible(epsilon, deltas, signals, times, measurements))
    clauses.extend(declare_helpers(str(formula)))
    clauses.append('(check-sat)')

    # create file with clauses
    with open(file, 'w') as f:
        for clause in clauses:
            f.write(clause + '\n')
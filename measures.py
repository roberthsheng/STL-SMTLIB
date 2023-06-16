import re
import csv
import pandas

def is_possible(epsilon, deltas, signals, times, measurements):
    # assume epsilons[signal] is bound for signal
    # assume deltas[signal][time] is bound for signal at time
    clauses = []
    for signal in signals:
        clauses.append('(declare-const o' + str(signal) + ' Real)')
        clauses.append('(assert (and (<= (- ' + str(epsilon[signal]) + ') o' + str(signal) + ') (<= o' + str(signal) + ' ' + str(epsilon[signal]) + ')))')
        for time in times:
            clauses.append('(declare-const e' + str(signal) + str(time) + ' Real)')
            clauses.append('(assert (and (<= (- ' + str(deltas[signal][time]) + ') xe' + str(signal) + str(time) + ') (<= e' + str(signal) + str(time) + ' ' + str(deltas[signal][time]) + ')))')

    # for measure in measurements declare and assert

    # relations between measurements and states
    for measure in measurements:
        clauses.append('(assert (= (+ ' + str(measure)[1:] + ' o' + str(measure)[1] + ' e' + str(measure)[1:] + ') ' + str(measure) + '))')

    return clauses

def declare_helpers(formula):
    clauses = []
    # turn all instances of "pi" in formula into declared Bools, where i is a natural number
    helperPattern = r'pi\d+'
    varPattern = r'(?![p])[a-z]\d+'

    for pi in list(set(re.findall(helperPattern, formula))):
        clauses.append('(declare-const ' + pi + ' Bool)')
    
    for xi in list(set(re.findall(varPattern, formula))):
        clauses.append('(declare-const ' + xi + ' Real)')
        # Do we need to create bounds for xi? If so, #HACK
        # clauses.append('(assert (and (<= (- 9999999999999) ' + xi + ') (<= ' + xi + ' 9999999999999)))')

    # assumes original variables have already been declared
    clauses.append('(assert ' + formula + ')')
    return clauses

# TODO: define way to pass in measurements
def measured(timeseries_csv):
    # csv with columns: signal, time, epsilon, delta, measurement
    pandas.read_csv(timeseries_csv)
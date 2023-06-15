import re
from z3 import *

def decompose(formula):
    operation = None
    operands = []
    depth = 0
    operand = ""
    for char in formula:
        if char == '(':
            if depth > 0:
                operand += char
            depth += 1
        elif char == ')':
            depth -= 1
            if depth > 0:
                operand += char
            elif operand:
                operands.append(operand.strip())
                operand = ""
        elif char == ' ' and depth == 1:
            if operand:
                if operation is None:
                    operation = operand
                else:
                    operands.append(operand)
                operand = ""
        elif depth > 0:
            operand += char
    return operation, operands

def tseitin_transformation(formula, mapping, counter):
    if formula in ['true', 'false', '⊤', '⊥']:
        return formula, counter
    if formula[0] != '(':
        return formula, counter
    operation, operands = decompose(formula)
    new_operands = []
    for operand in operands:
        new_formula, new_counter = tseitin_transformation(operand, mapping, counter)
        counter = new_counter
        new_operands.append(new_formula)
    new_formula = f'({operation} {" ".join(new_operands)})'
    counter += 1
    new_variable = f'p{counter}'
    mapping[new_variable] = new_formula

    if operation == 'not':
        mapping['clauses'].append([new_variable, new_operands[0]])
        mapping['clauses'].append([f'not {new_variable}', f'not {new_operands[0]}'])
    elif operation == 'and':
        for operand in new_operands:
            mapping['clauses'].append([f'not {new_variable}', operand])
        mapping['clauses'].append([new_variable] + [f'not {operand}' for operand in new_operands])
    elif operation == 'or':
        for operand in new_operands:
            mapping['clauses'].append([new_variable, f'not {operand}'])
        mapping['clauses'].append([f'not {new_variable}'] + new_operands)

    return new_variable, counter

def tseitin_to_cnf(formula):
    mapping = {'clauses': []}
    counter = 0
    new_formula, counter = tseitin_transformation(formula, mapping, counter)
    mapping['clauses'].append([new_formula])

    # Add back the non-boolean operations
    for var, form in mapping.items():
        if var not in ['clauses', new_formula] and form[0] == '(':
            mapping['clauses'].append([var, form])
            mapping['clauses'].append([f'not {var}', f'not {form}'])

    return mapping['clauses'], mapping


def cnf_to_z3(cnf_list):
    vars = {}
    z3_vars = {}

    def get_var(lit):
        nonlocal vars, z3_vars
        var = lit.replace('not ', '')
        if var not in vars:
            vars[var] = Bool(var)
            z3_vars[var] = vars[var]
        return (Not(z3_vars[var]) if 'not ' in lit else z3_vars[var])

    clauses = []
    for clause in cnf_list:
        new_clause = []
        for lit in clause:
            if lit == 'true':
                new_clause.append(True)
            elif lit == 'false':
                new_clause.append(False)
            elif isinstance(lit, list):  # Treat list as a conjunction
                subclause = []
                for sublit in lit:
                    subclause.append(get_var(sublit))
                new_clause.append(And(*subclause))
            else:
                new_clause.append(get_var(lit))
        clauses.append(Or(*new_clause))

    return vars, And(*clauses)


def interpret_model(model, mapping):
    interpretation = {}
    for variable in model:
        if variable in mapping:
            p_variable = mapping[variable]
            value = model[variable]
            interpretation[p_variable] = {
                'value': value,
                'original_variable': variable
            }
    return interpretation


def evaluate(transformed, mapping):
    vars, clauses = cnf_to_z3(transformed)
    solver = Solver()
    solver.add(clauses)

    if solver.check() == sat:
        model = solver.model()
        assignment = {str(var): model.evaluate(var) for var in vars.values()}
        print("Tseitin assignment: ", assignment)

        # interpret the assignment
        interpretation = interpret_model(assignment, mapping)
        print("Interpretation: ", interpretation)

        return True
    else:
        print("UNSAT")
        return False

def cnf_to_smt(cnf_list):
    smt_list = []
    for clause in cnf_list:
        smt_list.append(f'(or {" ".join("(" + lit + ")" if "not" in lit else lit for lit in clause)})')
    return f'(and {" ".join(smt_list)})'
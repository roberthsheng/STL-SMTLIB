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
        # Don't create a new variable if the formula is a literal
        return formula, counter
    operation, operands = decompose(formula)
    new_operands = []
    for operand in operands:
        new_formula, new_counter = tseitin_transformation(operand, mapping, counter)
        counter = new_counter
        new_operands.append(new_formula)
    new_formula = f'({operation} {" ".join(new_operands)})'

    # Introduce new variable for sub-formula
    counter += 1
    new_variable = f'p{counter}'
    mapping[new_variable] = new_formula

    if operation == 'not':
        mapping['clauses'].append([new_variable, new_operands[0]])
        mapping['clauses'].append([f'not {new_variable}', f'not {new_operands[0]}'])
    elif operation == 'and':
        clause = [new_variable] + [f'not {operand}' for operand in new_operands]
        mapping['clauses'].append(clause)
        for i in range(len(new_operands)):
            mapping['clauses'].append([f'not {new_variable}', new_operands[i]])
            mapping['clauses'].append([f'not {new_variable}', f'not {new_operands[i]}', new_variable])
    elif operation == 'or':
        mapping['clauses'].append([f'not {new_variable}'] + new_operands)
        for operand in new_operands:
            mapping['clauses'].append([new_variable, f'not {operand}'])

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

    return mapping['clauses']



def cnf_to_smt(cnf):
    # create a list to hold disjunctions
    disjunctions = []
    for clause in cnf:
        # wrap each literal in the clause with parentheses
        clause_strs = ['(' + literal + ')' for literal in clause]
        # join literals in the clause with 'or', wrap it into parentheses to represent a disjunction
        disjunction = '(or ' + ' '.join(clause_strs) + ')'
        disjunctions.append(disjunction)
    # join all disjunctions with 'and', wrap it into parentheses to represent a conjunction
    conjunction = '(and ' + ' '.join(disjunctions) + ')'
    return conjunction


def cnf_to_z3(cnf_list):
    vars = {}
    z3_vars = {}

    def get_var(lit):
        nonlocal vars, z3_vars
        var = lit.replace('not ', '')
        var = re.sub(r'\(([^)]+)\)', r'\1', var)  # Remove parentheses if present
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
            elif lit.startswith('(and'):
                lits = lit[lit.index(' ') + 1:-1].split(' ')
                new_clause.extend([get_var(sublit) for sublit in lits])
            elif lit.startswith('(or'):
                lits = lit[lit.index(' ') + 1:-1].split(' ')
                new_clause.append(Or(*[get_var(sublit) for sublit in lits]))
            else:
                new_clause.append(get_var(lit))
        clauses.append(Or(*new_clause))

    return vars, And(*clauses)

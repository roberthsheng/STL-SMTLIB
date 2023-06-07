import re

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
        mapping[formula] = formula
        return formula, counter
    operation, operands = decompose(formula)
    new_operands = []
    for operand in operands:
        new_formula, new_counter = tseitin_transformation(operand, mapping, counter)
        counter = new_counter
        new_operands.append(new_formula)
    new_formula = f'({operation} {" ".join(new_operands)})'
    if operation not in ['not', 'and', 'or', '>=', '*', '+']:
        raise ValueError(f'Unexpected operation {operation}')
    
    # Introduce new variable for sub-formula
    counter += 1
    new_variable = f'p{counter}'

    if operation in ['not', 'and', 'or']:
        if operation == 'not':
            mapping['clauses'].append([f'{new_variable}', new_operands[0]])
            mapping['clauses'].append([f'not {new_variable}', f'not {new_operands[0]}'])
        else:
            clause = [f'not {new_variable}'] + new_operands
            mapping['clauses'].append(clause)
            for operand in new_operands:
                mapping['clauses'].append([new_variable, f'not {operand}'])
    elif operation in ['>=', '*', '+']:
        # For non-boolean operations, simply map the new_variable directly to the new_formula
        mapping[new_variable] = new_formula

    return new_variable, counter

def tseitin_to_cnf(formula):
    mapping = {'clauses': []}
    counter = 0
    new_formula, counter = tseitin_transformation(formula, mapping, counter)
    mapping['clauses'].append([new_formula])

    # Add back the non-boolean operations
    for var, form in mapping.items():
        if var not in ['clauses', new_formula] and form[0] == '(':
            mapping['clauses'].append([f'{var}', form])
            mapping['clauses'].append([f'not {var}', f'not {form}'])

    return mapping['clauses']

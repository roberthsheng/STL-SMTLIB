import compiler, trajectory, measures, tseitin

tests = [
    # ("⊤"), 
    # ("⊥"), 
    # ("¬x"), 
    # ("x ∨ y"), 
    # ("x ∧ ¬y"), 
    # ("¬(x ∧ y)"), 
    # ("⊤ ∨ x"), 
    # ("⊥ ∧ x"), 
    # ("⊥ ∧ ⊥"), 
    # ("¬(⊤ ∨ x)"),
    # ("¬(⊥ ∧ x)"),
    # ("⊤ U[0, 5] ⊥"),
    ("(x ≥ 3) U[1, 3] (z ≥ 2)"),
    # ("(x ≥ 3) U[0, 10] (y ≥ 5)"),
    # ("(a + b ≥ 4) U[2, 4] (c ≥ 2)"),
    # ("(x ≥ 3) U[0, 10] (y ≥ 5) ∧ (z ≥ 2)"),
    # ("(y ≥ 5) ∧ (z ≥ 2) U[0, 10] (x ≥ 3)"),
    # ("¬(y ≥ 5) ∧ ⊤ U[0, 10] ⊥"),
    # ("2.95x ≥ 9"),
    # ("3x + 2y ≥ 9"),
    # ("(2a + b ≥ 4) U[2, 5] (3c ≥ 2)"),
    # ("2x ≥ 6 ∧ 3y ≥ 9"),
    # ("¬(4.5y ≥ 20) ∧ ⊤ U[0, 10] ⊥"),
    # ("1 ≥ 2")
]

def main():
    for stl in tests:
        smtlib = compiler.stl_to_smtlib(stl)
        print(stl)
        print(smtlib)
        transformed, mapping = tseitin.tseitin_to_cnf(smtlib)
        formula = tseitin.cnf_to_smt(transformed)

        

        print()

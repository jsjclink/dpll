import copy
import sys
import re


class DPLL:
    # assignment element. either imply or decision
    class AssignmentElem:
        def __init__(self, truth_val, imp_clauses, depth):
            self.truth_val = truth_val
            self.imp_clauses = imp_clauses
            self.depth = depth

        def __str__(self):
            return f"truth_val: {self.truth_val}, imp_clauses: {self.imp_clauses}, depth: {self.depth}"

    # parse cnf formula from input file
    def __init__(self):
        # read file
        if len(sys.argv) < 2:
            sys.exit(1)

        filename = sys.argv[1]

        with open(filename, "r") as f:
            data = f.read()

        cnf_formula = set()
        acc_literal_lst = []
        num_vars, num_clauses = 0, 0

        # parse
        for line in data.splitlines():
            if line.isspace() or len(line) == 0:
                continue
            elif re.search("^c.*", line):
                continue
            elif match_pcnf := re.search(r"^p cnf (\d+) (\d+)", line):
                num_vars = int(match_pcnf.group(1))
                num_clauses = int(match_pcnf.group(2))
            else:
                literal_lst = [int(x) for x in re.findall(r"-?\d+", line)]
                acc_literal_lst = acc_literal_lst + literal_lst
                if 0 in acc_literal_lst:
                    acc_literal_lst.remove(0)
                    cnf_formula.add(frozenset(acc_literal_lst))
                    acc_literal_lst = []

        # store cnf_formula
        self.cnf_formula = cnf_formula
        # prop_val: assignment_elem
        self.assignment = {}
        self.num_vars, self.num_clauses = num_vars, num_clauses

    # do dpll
    def dpll(self):
        while True:
            self.unit_prop()
            f_a = self.calculate_f_a()
            if len(f_a) == 0:
                return self.assignment
            elif frozenset() in f_a:
                clause = self.learn()
                if len(clause) == 0:
                    return None
                while self.find_unit_clause():
                    self.assignment.popitem()
            else:
                for i in range(1, self.num_vars + 1):
                    if not i in self.assignment.keys():
                        print(i)
                        self.assignment[i] = self.AssignmentElem(
                            False, [], len(self.assignment)
                        )
                        break

    def unit_prop(self):
        while res := self.find_unit_clause():
            prop_var, truth_val, imp_clauses = res
            self.assignment[prop_var] = self.AssignmentElem(
                truth_val, imp_clauses, len(self.assignment)
            )

    def find_unit_clause(self):
        for clause in self.cnf_formula:
            if self.is_true_clause(clause):
                continue
            if literal := self.find_unit_literal(clause):
                imp_clauses = []
                for clause in self.cnf_formula:
                    if not self.is_true_clause(clause) and literal in clause:
                        imp_clauses.append(clause)
                return abs(literal), (True if literal > 0 else False), imp_clauses
        return None

    # check if the clause is true by assignment
    def is_true_clause(self, clause):
        for prop_var, assign_elem in self.assignment.items():
            literal = prop_var if assign_elem.truth_val else -prop_var
            if literal in clause:
                return True
        return False

    # inv: caluse is not true by original assignment.
    # return literal of unit clause
    def find_unit_literal(self, clause):
        tmp_c = set(clause)
        for prop_var in self.assignment.keys():
            if prop_var in tmp_c:
                tmp_c.remove(prop_var)
            if (-prop_var) in tmp_c:
                tmp_c.remove((-prop_var))
        if len(tmp_c) == 1:
            literal = tmp_c.pop()
            return literal
        else:
            return None

    def calculate_f_a(self):
        tmp_cnf = set()
        for clause in self.cnf_formula:
            if self.is_true_clause(clause):
                continue
            tmp_c = set(clause)
            for prop_var, assign_elem in self.assignment.items():
                literal = -prop_var if assign_elem.truth_val else prop_var
                # remove literal|-> false from clause
                if literal in clause:
                    tmp_c.remove(literal)
            tmp_cnf.add(frozenset(tmp_c))
        return tmp_cnf

    def find_conflict_clause(self):
        

    def learn(self):
        

        return set()


if __name__ == "__main__":
    dpll = DPLL()
    assignment = dpll.dpll()
    if assignment:
        print("SAT!")
        for prop_val, assignment_elem in assignment.items():
            print(f"prop_val: {prop_val}, ", end="")
            print(assignment_elem)
    else:
        print("UNSAT!")
    print(dpll.cnf_formula)

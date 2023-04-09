import copy
import sys
import re


class DPLL:
    # assignment element. either implied (by clause) or decision
    class AssignmentElem:
        def __init__(self, truth_val, imply_clause):
            self.truth_val = truth_val
            self.imply_clause = imply_clause

        def __str__(self):
            return f"truth_val: {self.truth_val}, imply_clause: {self.imply_clause}"

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

        # infornations
        self.num_vars, self.num_clauses = num_vars, num_clauses
        # store cnf_formula
        self.cnf_formula = cnf_formula
        # prop_val|-> assignment_elem
        self.assignment = {}
        # prop_val|-> depth map
        self.depth_map = {}

    # dpll algorithm
    def dpll(self):
        while True:
            f_a = self.unit_prop()
            if len(f_a) == 0:
                return self.assignment
            elif frozenset() in f_a.keys():
                print(f_a[frozenset()])
                clause = self.learn(f_a[frozenset()])
                if len(clause) == 0:
                    return None
                while self.is_unit_clause(clause):
                    self.assignment.popitem()
            else:
                for i in range(1, self.num_vars + 1):
                    if i in self.assignment.keys():
                        continue
                    self.add_assignment(i, self.AssignmentElem(False, None))
                    break

    def unit_prop(self):
        f_a = self.calculate_f_a()
        while res := self.find_unit_clause_with_f_a(f_a):
            prop_var, truth_val, imply_clause = res
            self.add_assignment(prop_var, self.AssignmentElem(truth_val, imply_clause))
            f_a = self.update_f_a(f_a)
        return f_a

    def learn(self, conflict_clause):
        return set()

    # util functions
    def add_assignment(self, prop_var, assignment_elem):
        self.depth_map[prop_var] = len(self.assignment)
        self.assignment[prop_var] = assignment_elem

    def is_true_clause(self, clause):
        for prop_var, assign_elem in self.assignment.items():
            literal_assigned_true = prop_var if assign_elem.truth_val else -prop_var
            if literal_assigned_true in clause:
                return True
        return False

    def is_unit_clause(self, clause):
        tmp_clause = set(clause)
        for prop_var, assign_elem in self.assignment.items():
            literal_assigned_false = -prop_var if assign_elem.truth_val else prop_var
            if literal_assigned_false in tmp_clause:
                tmp_clause.remove(literal_assigned_false)
        if len(tmp_clause) == 1:
            return True
        else:
            return False

    def find_unit_clause_with_f_a(self, f_a):
        for clause in f_a.keys():
            if not len(clause) == 1:
                continue
            imply_clause = f_a[clause]
            tmp_clause = set(clause)
            literal = tmp_clause.pop()
            return abs(literal), (True if literal > 0 else False), imply_clause
        return None

    def calculate_f_a(self):
        f_a = {}
        for clause in self.cnf_formula:
            if self.is_true_clause(clause):
                continue
            tmp_clause = set(clause)
            for prop_var, assign_elem in self.assignment.items():
                literal_assigned_false = (
                    -prop_var if assign_elem.truth_val else prop_var
                )
                if literal_assigned_false in tmp_clause:
                    tmp_clause.remove(literal_assigned_false)
            f_a[frozenset(tmp_clause)] = clause

        return f_a

    def update_f_a(self, f_a):
        new_f_a = {}
        for clause in f_a.keys():
            if self.is_true_clause(clause):
                continue
            tmp_clause = set(clause)
            for prop_var, assign_elem in self.assignment.items():
                literal_assigned_false = (
                    -prop_var if assign_elem.truth_val else prop_var
                )
                if literal_assigned_false in tmp_clause:
                    tmp_clause.remove(literal_assigned_false)
            new_f_a[frozenset(tmp_clause)] = f_a[clause]

        return new_f_a


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

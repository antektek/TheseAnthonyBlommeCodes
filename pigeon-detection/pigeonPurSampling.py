#!/usr/bin/python3

########################################## Imports ##############################################

import sys
from copy import deepcopy
from math import log2
import signal

######################################### Functions #############################################

# Update the marks of a literal or a clause
def updateMark(marks, index, marker):
    if marker > 0:
        marks[index] |= (1 << (marker - 1))

# Perform the unit propagation (do not stop at the first conflict)
def unit_propagation(cnf, literal, marksLiterals, marker, nVariables):
    to_propagate = [literal]
    propagated = []
    for i in range(2 * nVariables + 1):
        assigned[i] = 0
        toAssign[i] = 0
    while to_propagate != []:
        # We propagate the first literal in the list
        propagate = to_propagate.pop(0)
        propagated.append(propagate)
        assigned[propagate] = 1
        toAssign[propagate] = 0
        if propagate != literal:
            updateMark(marksLiterals, -propagate, marker)
        # Look for the simplified clauses
        for indClause in range(len(cnf)):
            if -propagate in cnf[indClause]:
                diff = None
                for lit in cnf[indClause]:
                    if assigned[-lit] == 0:
                        if diff is None:
                            diff = lit
                        else:
                            diff = None
                            break
                if diff is not None:
                    # We have found a unit clause
                    if assigned[diff] == 0 and toAssign[diff] == 0:
                        to_propagate.append(diff)
                        toAssign[diff] = 1
    return propagated

# Mark the clauses and literals according to the unit propagation of each literal of a clause
def analyseClause(cnf, indClause, nVariables):
    marker = 0
    marksLiterals = [0] * (2 * nVariables + 1)
    for literal in cnf[indClause]:
        marker += 1
        updateMark(marksLiterals, literal, marker)
        unit_propagation(cnf, literal, marksLiterals, marker, nVariables)
    return marksLiterals

# Perform a unit propagation with the bitmasks
def unitPropagationBitmask(marks, remove, lenClause):
    toRm = [remove]
    exclude = [-1]
    toDo = [0] * lenClause
    done = [0] * lenClause
    newMarks = marks.copy()
    while toRm != []:
        # Get the next mark to remove from the bitmasks
        rm = toRm.pop(0)
        excl = exclude.pop(0)
        if rm >= 0:
            toDo[rm] = 0
            done[rm] = 1
        for indMark in range(len(marks)):
            if indMark != excl:
                if rm >= 0:
                    newMarks[indMark] &= ~(1 << rm)
                if newMarks[indMark] == 0:
                    # Empty bitmask
                    return []
                if newMarks[indMark] & (newMarks[indMark] - 1) == 0:
                    # Bitmask with only one mark 1
                    newRemove = int(log2(newMarks[indMark]))
                    if toDo[newRemove] == 0 and done[newRemove] == 0:
                        toRm.append(newRemove)
                        exclude.append(indMark)
                        toDo[newRemove] = 1
    return newMarks

# Create all the possible combinations of marks for a clause
def combinations(clause, marks, combi):
    if len(marks) == 0:
        return [combi.copy()] if len(combi) == len(clause) else []
    combs = []
    bitmask = marks.pop(0)
    for i in range(len(clause)):
        if (bitmask & 1 << i) != 0:
            simplified = unitPropagationBitmask(marks, i, len(clause))
            combi.append(1 << i)
            combis = combinations(clause, simplified, combi)
            combi.pop()
            combs += [c for c in combis if c not in combs]
    return combs

# Check if a clause can be selected to construct a pigeon hole
def canSelect(formula, currentClause, current, nVariables):
    for indLiteral in range(len(currentClause)):
        # Try to find the exclusions for each literal in the clause
        findLiterals = [-cl[indLiteral] for cl in current]
        propagations = unit_propagation(formula, currentClause[indLiteral], [], 0, nVariables)
        for lit in findLiterals:
            if lit not in propagations:
                return False
    return True

# Try to construct a pigeon hole starting from a specific clause
def pigeonHoleConstruction(formula, clause, remainingClauses, currentPigeon, knownPigeons, nVariables):
    if len(currentPigeon) > len(clause):
        # We have found a new pigeon hole problem
        newPigeon = deepcopy(currentPigeon)
        newPigeon.sort(key=(lambda x : abs(x[0])))
        #print("pigeon =", newPigeon)
        if newPigeon not in knownPigeons:
            knownPigeons.append(newPigeon)
    else :
        # Try to expand the current pigeon hole by selecting a new clause in the remaining ones
        for indCl in range(len(remainingClauses)):
            if canSelect(formula, remainingClauses[indCl], currentPigeon, nVariables):
                # Select the remaining clauses
                remain = []
                for indRemain in range(indCl + 1, len(remainingClauses)):
                    selectRemain = True
                    for lit in remainingClauses[indRemain]:
                        if lit in remainingClauses[indCl]:
                            selectRemain = False
                            break
                    if selectRemain:
                        remain.append(remainingClauses[indRemain].copy())
                # Next iteration of the constrcution
                if (len(remain) + len(currentPigeon) + 1) > len(clause):
                    currentPigeon.append(remainingClauses[indCl])
                    pigeonHoleConstruction(formula, clause, remain, currentPigeon, knownPigeons, nVariables)
                    currentPigeon.pop()
                    if knownPigeons != []:
                        break

def pigeonHoleDetection(formula, indClause, nVariables, knownPigeons, blocked):
    marksLiterals = analyseClause(formula, indClause, nVariables)
    correspClauses = []
    for indCand in range(len(formula)):
        if blocked[indCand] == 0 and len(formula[indCand]) == len(formula[indClause]):
            # Create the combinations
            marks = unitPropagationBitmask([marksLiterals[lit] for lit in formula[indCand]], -1, len(formula[indClause]))
            if marks != []:
                combis = combinations(formula[indClause], marks, [])
                # Reorder the literals for each combination
                reorder = [formula[indCand].copy() for _ in range(len(combis))]
                for ind in range(len(reorder)):
                    cl = reorder[ind].copy()
                    reorder[ind].sort(key=(lambda x : combis[ind][cl.index(x)]))
                correspClauses += reorder
    # Try to construct pigeon hole problems
    if len(correspClauses) + 1 > len(formula[indClause]):
        pigeonHoleConstruction(formula, formula[indClause], correspClauses, [formula[indClause]], knownPigeons, nVariables)

# Perform the unit propagation (stop at the first conflict)
def unit_propagation_sampling(cnf, literal, assignment, nVariables):
    to_propagate = [literal]
    for i in range(2 * nVariables + 1):
        assigned[i] = 0
        toAssign[i] = 0
    propagated = []
    for lit in assignment:
        propagated.append(lit)
        assigned[lit] = 1
    while to_propagate != []:
        # We propagate the first literal in the list
        propagate = to_propagate.pop(0)
        propagated.append(propagate)
        assigned[propagate] = 1
        toAssign[propagate] = 0
        # Look for the simplified clauses
        for indClause in range(len(cnf)):
            if -propagate in cnf[indClause] or propagate == 0:
                n, diff = 0, None
                for lit in cnf[indClause]:
                    if assigned[-lit] == 0:
                        n += 1
                        if diff is None:
                            diff = lit
                        else:
                            break
                if n == 0:
                    # UNSAT
                    return ("UNSAT", propagated)
                if n == 1:
                    # We have found a unit clause
                    if assigned[diff] == 0 and toAssign[diff] == 0:
                        to_propagate.append(diff)
                        toAssign[diff] = 1
    return ("UNKNOWN", propagated)

# Chose the next variable (next decision)
def choseNextVariable(nVariables, assignment, heuris):
    if heuris != []:
        return heuris.pop(0)
    for i in range(1, nVariables + 1):
        if i not in assignment and -i not in assignment:
            return i
    return None

# Perform a DPLL Search
def dpllSearch(formula, nextPropagation, decisions, assignment, nVariables, branches, correspAssign):
    global cptBranch, nBranches, longuestBranch
    ans, assign = unit_propagation_sampling(formula, nextPropagation, assignment, nVariables)
    if ans == "UNKNOWN":
        # Chose the next variable to decide
        nextVar = choseNextVariable(nVariables, assign, [])
        if nextVar is None:
            # SAT
            return
        # Left child
        decisions.append(-nextVar)
        dpllSearch(formula, -nextVar, decisions, assign, nVariables, branches, correspAssign)
        decisions.pop()
        if len(branches) >= maxBranches:
            return
        # Right child
        decisions.append(nextVar)
        dpllSearch(formula, nextVar, decisions, assign, nVariables, branches, correspAssign)
        decisions.pop()
    else:
        # Check if we take into account the current branch
        cptBranch = (cptBranch + 1) % ratioBranches
        if cptBranch == 0:
            if len(decisions) > longuestBranch:
                longuestBranch = len(decisions)
            branches.append(decisions.copy())
            correspAssign.append(assign[1::])

# Simplify a formula according to some assignments
def simplifyFormula(formula, assignment):
    result = []
    for clause in formula:
        newCl = []
        for lit in clause:
            if lit in assignment:
                newCl = []
                break
            if -lit in assignment:
                continue
            newCl.append(lit)
        if newCl != []:
            result.append(newCl.copy())
    return result

# Try to find some pigeons on the selected branches
def tryDetection(formula, branches, allAssignments, maxLengthBranch):
    explored = []
    for back in range(1, maxLengthBranch + 1):
        for indBranch in range(len(branches)):
            if back <= len(branches[indBranch]):
                # Get the corresponding decisions and assignment
                lastDecision = branches[indBranch][-back]
                ind = allAssignments[indBranch].index(lastDecision)
                decisions = branches[indBranch][:len(branches[indBranch]) - back:]
                assign = allAssignments[indBranch][:ind:]
                if decisions not in explored:
                    # Simplify the formula and try to find pigeons
                    form = simplifyFormula(formula, assign)
                    knownPigeons = []
                    blocked = [0] * len(form)
                    for indClause in range(len(form)):
                        blocked[indClause] = 1
                        if len(form[indClause]) > 1 and len(form[indClause]) <= maxPigeons:
                            print(form[indClause])
                            pigeonHoleDetection(form, indClause, n_variables, knownPigeons, blocked)
                            if knownPigeons != []:
                                break
                    if knownPigeons == []:
                        print(decisions, "-> []\n")
                    else:
                        if str(knownPigeons[0]) not in known:
                            atleasts = len(knownPigeons[0])
                            atmosts = len(knownPigeons[0][0])
                            if (atleasts, atmosts) not in cptSize:
                                cptSize[(atleasts, atmosts)] = 0
                            cptSize[(atleasts, atmosts)] += 1
                            name = "ph" + str(atleasts) + "-" + str(atmosts) + "_" + str(cptSize[(atleasts, atmosts)])
                            known[str(knownPigeons[0])] = name
                        print(decisions, "->", known[str(knownPigeons[0])], "\n")
                    explored.append(decisions)

# Print the detected pigeons if the SIGINT signal is received
def handler(signum, frame):
    print("\nDetected pigeons:")
    for pigeon in known:
        print("\n", known[pigeon], "=", pigeon)
    exit(1)

############################################ Main ###############################################


# parameters
if len(sys.argv) != 2:
	print("usage : python3 pigeonPurSampling.py instance.cnf")
	print("usage : ./pigeonPurSampling.py instance.cnf")
	exit(1)

filename = sys.argv[1]

# Read the instance
file = open(filename, "r")
lines = file.readlines()
file.close()

# Get the formula
formula = []
for line in lines:
    if line[0] == 'p':
        n_variables = int(line.split()[2])
        n_clauses = int(line.split()[3])
        assigned = [0] * (2 * n_variables + 1)
        toAssign = [0] * (2 * n_variables + 1)
    elif line[0] != 'c':
        formula.append(list(map(int, line.split()[0:-1])))

maxPigeons = 64
minPigeons = 2

known = {}
cptSize = {}
signal.signal(signal.SIGINT, handler)

ratioBranches = 100
maxBranches = 100

cptBranch = -1
longuestBranch = 0
chosedBranches = []
correspAssignments = []
dpllSearch(formula, 0, [], [], n_variables, chosedBranches, correspAssignments)
tryDetection(formula, chosedBranches, correspAssignments, longuestBranch)

# print all the detected pigeons
print("\nDetected pigeons:")
for pigeon in known:
    print("\n", known[pigeon], "=", pigeon)

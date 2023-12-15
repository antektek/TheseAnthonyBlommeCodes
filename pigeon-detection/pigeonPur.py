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

# Update the clauses we have to consider for the pigeon hole detection
def updateConsider(cnf, exclusion, consider):
    for indClause in range(len(cnf)):
        if not consider[indClause]:
            if -exclusion[0] in cnf[indClause] or -exclusion[1] in cnf[indClause]:
                consider[indClause] = True
                if len(cnf[indClause]) == 2:
                    updateConsider(cnf, cnf[indClause], consider)

# Perform the unit propagation (DPLL version - stop at the first conflict)
def unit_propagation_dpll(cnf, current, literal, assignment, consider):
    to_propagate = [literal]
    propagated = assignment.copy()
    assigned = [0] * (2 * n_variables + 1)
    toAssign = [0] * (2 * n_variables + 1)
    propCl = {}
    result = deepcopy(current)
    while to_propagate != []:
        # We propagate the first literal in the list
        propagate = to_propagate.pop(0)
        if propagate != 0:
            propagated.append(propagate)
        assigned[propagate] = 1
        toAssign[propagate] = 0
        # Look for the simplified clauses
        for indClause in range(len(result)):
            if propagate in result[indClause]:
                # Remove the clause
                result[indClause] = []
            elif -propagate in result[indClause] or propagate == 0:
                if propagate != 0:
                    result[indClause].remove(-propagate)
                    consider[indClause] = True
                    if len(result[indClause]) == 2:
                        updateConsider(cnf, result[indClause], consider)
                if len(result[indClause]) == 0:
                    # Empty clause -> UNSAT
                    return ("UNSAT", propagated, propCl, cnf[indClause].copy(), result)
                if len(result[indClause]) == 1:
                    # We have found a unit clause
                    if assigned[result[indClause][0]] == 0 and toAssign[result[indClause][0]] == 0:
                        to_propagate.append(result[indClause][0])
                        propCl[str(result[indClause][0])] = cnf[indClause].copy()
                        toAssign[result[indClause][0]] = 1
    return ("UNKNOWN", propagated, propCl, [], result)

# Chose the next variable (next decision)
def choseNextVariable(nVariables, assignment, heuris):
    if heuris != []:
        return heuris.pop(0)
    for i in range(1, nVariables + 1):
        if i not in assignment and -i not in assignment:
            return i
    return None

# Find the first clause of size >= 3 using the propagations 
def backtrackPropagations(propClauses, currentLiteral):
    if str(currentLiteral) in propClauses:
        cl = propClauses[str(currentLiteral)].copy()
        if len(cl) > 2:
            # We have found a starting clause
            return cl
        elif len(cl) == 2:
            # We have a binary clause, we keep backtracking
            cl.remove(currentLiteral)
            nextLit = -cl[0]
            return backtrackPropagations(propClauses, nextLit)
    return []

# Perform the pigeon hole detection on each clause we have to consider
def pigeonPur(formula, consider):
    knownPigeons = []
    blocked = [0] * n_clauses
    for indClause in range(len(formula)):
        if consider[indClause] > 0:
            blocked[indClause] = 1
            if len(formula[indClause]) >= minPigeons and len(formula[indClause]) <= maxPigeons:
                pigeonHoleDetection(formula, indClause, n_variables, knownPigeons, blocked)
                if knownPigeons != []:
                    break
    return knownPigeons

# Check if some literals are not concerned by the pigeon hole
def findGras(pigeon, literals):
    notGras, gras = [], []
    for lit in literals:
        isGras = True
        for clause in pigeon:
            if -lit in clause or lit in clause:
                isGras = False
                break
        if isGras:
            gras.append(lit)
        else:
            notGras.append(lit)
    return (notGras, gras)

# Simplify the current formula to prepare the pigeon hole detection
def updateAnswer(currentFormula, consider):
    cur, cons = [], []
    for indClause in range(len(currentFormula)):
        if currentFormula[indClause] != []:
            cur.append(currentFormula[indClause].copy())
            cons.append(consider[indClause])
    return pigeonPur(cur, cons)

# Preform a DPLL search on the formula
def dpll(formula, currentForm, nextPropagation, assignment, decisions, nVariables, level, heuris):
    if nextPropagation == 0:
    	toConsider = [1] * len(currentForm)
    else:
    	toConsider = [0] * len(currentForm)
    # Propagate the new decision 
    ans, assign, propCl, cl, current = unit_propagation_dpll(formula, currentForm, nextPropagation, assignment, toConsider)
    if ans == "UNKNOWN":
        pigeons = updateAnswer(current, toConsider)
        if pigeons == []:
     	    print(decisions, "-> []\n")
        else:
            # Check if the detected pigeon is already known
            if str(pigeons[0]) not in known:
        	    atleasts = len(pigeons[0])
        	    atmosts = len(pigeons[0][0])
        	    if (atleasts, atmosts) not in cptSize:
        		    cptSize[(atleasts, atmosts)] = 0
        	    cptSize[(atleasts, atmosts)] += 1
        	    name = "ph" + str(atleasts) + "-" + str(atmosts) + "_" + str(cptSize[(atleasts, atmosts)])
        	    known[str(pigeons[0])] = name
            print(decisions, "->", known[str(pigeons[0])], "\n")
            return [["UNSAT", level, known[str(pigeons[0])], decisions.copy(), assign]]
        # Chose the next variable
        nextVar = choseNextVariable(nVariables, assign, heuris)
        if nextVar is None:
            # SAT
            return [["SAT", assign]]
        # First child (negative decision)
        decisions.append(-nextVar)
        answer1 = dpll(formula, current, -nextVar, assign, decisions, nVariables, level + 1, heuris.copy())
        decisions.pop()
        lastAnswer = answer1[-1]
        if lastAnswer[0] == "SAT":
            return [lastAnswer]
        # Second child (positive decision)
        decisions.append(nextVar)
        answer2 = dpll(formula, current, nextVar, assign, decisions, nVariables, level + 1, heuris.copy())
        decisions.pop()
        lastAnswer = answer2[-1]
        if lastAnswer[0] == "SAT":
            return [lastAnswer]
        answer1.extend(answer2)
        return answer1
    else:
    	# UNSAT
        print(decisions, "-> UNSAT\n")
        return [["UNSAT", level, [], decisions.copy(), assign]]

# Print the detected pigeons if the SIGINT signal is received
def handler(signum, frame):
    print("\nDetected pigeons:")
    for pigeon in known:
        print("\n", known[pigeon], "=", pigeon)
    exit(1)

############################################ Main ###############################################


# parameters
if len(sys.argv) != 2:
	print("usage : python3 pigeonPur.py instance.cnf")
	print("usage : ./pigeonPur.py instance.cnf")
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
heuristique = []

signal.signal(signal.SIGINT, handler)

res = dpll(formula, formula, 0, [], [], n_variables, 0, heuristique)

# Print the final result
print("\nFinal result:")
for r in res:
    print(r)

# print all the detected pigeons
print("\nDetected pigeons:")
for pigeon in known:
    print("\n", known[pigeon], "=", pigeon)

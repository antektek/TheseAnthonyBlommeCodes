#!/usr/bin/python3

#################################################################################################
########################################## Imports ##############################################
#################################################################################################


import sys
from copy import deepcopy
from math import log2
import signal


#################################################################################################
######################################### Functions #############################################
#################################################################################################


####################################### Watch Literals ##########################################


# Add a new watch for a specific clause
def addWatch(watches, lit, other, clause):
    newWatch = []
    newWatch.append(other)
    if len(clause) > 2:
        newWatch.append(clause)
    watches[lit].append(newWatch)

# Add two watch literals to a clause
def watchClause(watches, clause):
    lit, other = clause[0], clause[1]
    addWatch(watches, lit, other, clause)
    addWatch(watches, other, lit, clause)

# Look for a replacing literal
def searchReplacement(watch, assigned):
    replacement, satisfied = None, False
    for ind in range(2, len(watch[1])):
        if assigned[watch[1][ind]] == 1:
            # The clause is satisfied
            satisfied = True
            break
        elif assigned[-watch[1][ind]] == 0:
            # We have found a replacement
            replacement = ind
            break
    return (replacement, satisfied)

# Update the watch literals concerned by a propagation
def replaceWatch(watches, notLit, assigned, toAssign, toProp, ignoreConflicts):
    for _ in range(len(watches[notLit])):
        w = watches[notLit].pop(0)
        # We check if the blocking literal satisfies the clause
        if assigned[w[0]] == 1:
            watches[notLit].append(w)
            continue
        # We check if we have a binary clause ...
        if len(w) == 1:
            watches[notLit].append(w)
            if assigned[-w[0]] == 1:
                # The blocking literal is falsified, we have a conflict
                if not ignoreConflicts:
                    return False
            elif assigned[w[0]] == 0 and toAssign[w[0]] == 0:
                # The blocking literal is unassigned, we propagate it
                toAssign[w[0]] = 1
                toProp.append(w[0])
        # ... or a longer clause
        else:
            # We get the falsified literal and the blocking literal and we reorganize the beginning of the clause
            block = w[1][0] ^ w[1][1] ^ notLit
            w[0] = block
            w[1][0] = notLit
            w[1][1] = block
            # We look for a replacement for the falsified literal
            replacement, satisfied = searchReplacement(w, assigned)
            if satisfied:
                # The clause is satisfied
                watches[notLit].append(w)
                continue
            if replacement is None:
                # There is no replacement
                watches[notLit].append(w)
                if assigned[-block] == 1:
                    # The blocking literal is falsified, we have a conflict
                    if not ignoreConflicts:
                        return False
                elif assigned[block] == 0 and toAssign[block] == 0:
                    # The blocking literal is unassigned, we propagate it
                    toAssign[block] = 1
                    toProp.append(block)
            else:
                # We have found a replacement, we swap it with the falsified literal
                w[1][0], w[1][replacement] = w[1][replacement], w[1][0]
                watches[w[1][0]].append(w)
    return True


###################################### Unit Propagation #########################################


# Update the marks of a literal or a clause
def updateMark(marks, index, marker):
    if marker > 0:
        marks[index] |= (1 << (marker - 1))

# Unassign literals assigned during the unit propagation
def undoPropagations(propagated, assigned, toAssign):
    for lit in propagated:
        assigned[lit] = 0
        toAssign[lit] = 0

# Simplify a specific clause after unit propagation
def simplifyClause(cnf, indClause, assigned):
    resClause = []
    for lit in cnf[indClause][1]:
        if assigned[lit] == 1:
            # The clause is satisfied, we erase it
            resClause = None
            break
        if assigned[-lit] == 1:
            # The literal is falsified, we don't take it into account
            continue
        resClause.append(lit)
    return resClause

# Update the clauses we have to consider for the pigeon hole detection
def updateConsider(cnf, exclusion, consider, assigned):
    for indClause in range(len(cnf)):
        # We check if the clause is not already considered and if it falsifies one of the
        # literals of the exclusion
        if not consider[cnf[indClause][0]]:
            if -exclusion[1][0] in cnf[indClause][1] or -exclusion[1][1] in cnf[indClause][1]:
                simpClause = simplifyClause(cnf, indClause, assigned)
                if simpClause is not None:
                    # The clause is not satisfied after the unit propagation, we have to consider it
                    consider[cnf[indClause][0]] = True
                    if len(simpClause) == 2:
                        # We have found a binary clause, we consider it as an exclusion
                        updateConsider(cnf, [cnf[indClause][0], simpClause], consider, assigned)

# Perform the unit propagation
def unitPropagation(cnf, literal, toPropagate, marksLiterals, marker, assigned, toAssign, watches, ignoreConflicts, keepModifs, toConsider):
    propagated, simpFormula = [], []
    while toPropagate != []:
        # We get the first literal to propagate
        propagate = toPropagate.pop(0)
        propagated.append(propagate)
        assigned[propagate] = 1
        toAssign[propagate] = 0
        # We mark the literal if it is different from the starting one
        if propagate != literal:
            updateMark(marksLiterals, -propagate, marker)
        if propagate != 0:
            # We update the watches concerned by the opposite of the propagated literal
            resWatch = replaceWatch(watches, -propagate, assigned, toAssign, toPropagate, ignoreConflicts)
            if not resWatch:
                # We have found an empty clause, so we have a conflict
                if not keepModifs:
                    undoPropagations(propagated, assigned, toAssign)
                while toPropagate != []:
                    a = toPropagate.pop()
                    toAssign[a] = 0
                return ("UNSAT", propagated, simpFormula)
    # If we don't want to keep the modificatons, we have to unassign the propagated literals
    if not keepModifs:
        undoPropagations(propagated, assigned, toAssign)
    # Otherwise, we simplify the formula
    else:
        for indClause in range(len(cnf)):
            simpClause = simplifyClause(cnf, indClause, assigned)
            if simpClause is not None:
                simpFormula.append([cnf[indClause][0], simpClause.copy()])
                if toConsider != [] and not toConsider[cnf[indClause][0]]:
                    # We have to consider a clause if it is not satisfied by the unit propagation
                    # and if it is smaller than the complete clause 
                    # (i.e. at least one literal is falsified)
                    if len(simpClause) < len(cnf[indClause][1]):
                        toConsider[cnf[indClause][0]] = True
                        if len(simpClause) == 2:
                            # We have found a binary clause, we consider it as an exclusion
                            updateConsider(cnf, [cnf[indClause][0], simpClause], toConsider, assigned)
    return ("UNKNOWN", propagated, simpFormula)


###################################### Pigeon Detection #########################################


# Mark the clauses and literals according to the unit propagation of each literal of a clause
def analyseClause(cnf, indClause, assigned, toAssign, watches, marksLiterals):
    marker = 0
    for literal in cnf[indClause][1]:
        marker += 1
        updateMark(marksLiterals, literal, marker)
        unitPropagation(cnf, literal, [literal], marksLiterals, marker, assigned, toAssign, watches, True, False, [])
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
        # Remove the mark from the bitmasks, except one
        for indMark in range(len(marks)):
            if indMark != excl:
                if rm >= 0:
                    newMarks[indMark] &= ~(1 << rm)
                if newMarks[indMark] == 0:
                    # Empty bitmask
                    return []
                if newMarks[indMark] & (newMarks[indMark] - 1) == 0:
                    # Bitmask with only one mark 1, we have to propagate the mark
                    newRemove = int(log2(newMarks[indMark]))
                    if toDo[newRemove] == 0 and done[newRemove] == 0:
                        toRm.append(newRemove)
                        exclude.append(indMark)
                        toDo[newRemove] = 1
    return newMarks

# Create all the possible combinations of marks for a clause
def combinations(clause, marks, combi):
    if len(marks) == 0:
        # A combination is good only if it is of the same size than the starting clause
        return [combi.copy()] if len(combi) == len(clause[1]) else []
    combs = []
    # We get the next bitmask
    bitmask = marks.pop(0)
    for i in range(len(clause[1])):
        # If we find a mark 1, we fix it for the current position and we propagate it 
        if (bitmask & 1 << i) != 0:
            simplified = unitPropagationBitmask(marks, i, len(clause[1]))
            combi.append(1 << i)
            # We consider the next bitmask
            combis = combinations(clause, simplified, combi)
            combi.pop()
            combs += [c for c in combis if c not in combs]
    return combs

# Check if a clause can be selected to construct a pigeon hole
def canSelect(formula, currentClause, current, assigned, toAssign, watches):
    for indLiteral in range(len(currentClause[1])):
        # Try to find the exclusions for each literal in the clause
        findLiterals = [-cl[1][indLiteral] for cl in current]
        literal = currentClause[1][indLiteral]
        # Check if we propagate all the exclusions
        _, propagations, _ = unitPropagation(formula, literal, [literal], [], 0, assigned, toAssign, watches, True, False, [])
        for lit in findLiterals:
            if lit not in propagations:
                return False
    return True

# Try to construct a pigeon hole starting from a specific clause
def pigeonHoleConstruction(formula, clause, remainingClauses, currentPigeon, knownPigeons, assigned, toAssign, watches):
    if len(currentPigeon) > len(clause[1]):
        # We have found a new pigeon hole problem
        newPigeon = deepcopy(currentPigeon)
        newPigeon.sort(key=(lambda x : x[0]))
        print("pigeon =", newPigeon)
        if newPigeon not in knownPigeons:
            knownPigeons.append(newPigeon)
    else :
        # Try to expand the current pigeon hole by selecting a new clause in the remaining ones
        for indCl in range(len(remainingClauses)):
            if canSelect(formula, remainingClauses[indCl], currentPigeon, assigned, toAssign, watches):
                # Select the remaining clauses
                remain = []
                selectedIndexes = []
                lastAnswer = False
                lastIndex = -1
                for indRemain in range(indCl + 1, len(remainingClauses)):
                    # If we have already encoutered the clause, we use the previous result
                    if lastIndex == remainingClauses[indRemain][0]:
                        if lastAnswer:
                            remain.append(remainingClauses[indRemain].copy())
                    else:
                        # Check if a clause doesn't intersect with the added clause 
                        selectRemain = True
                        for lit in remainingClauses[indRemain][1]:
                            if lit in remainingClauses[indCl][1] or -lit in remainingClauses[indCl][1]:
                                # The current clause intersects with the added clause, we don't consider it
                                selectRemain = False
                                break
                        if selectRemain:
                            # We add the current clause to the remaining ones
                            remain.append(remainingClauses[indRemain].copy())
                            selectedIndexes.append(remainingClauses[indRemain][0])
                        lastAnswer = selectRemain
                        lastIndex = indRemain
                # Next iteration of the construction if we have enough candidates
                if (len(selectedIndexes) + len(currentPigeon) + 1) > len(clause):
                    currentPigeon.append(remainingClauses[indCl])
                    pigeonHoleConstruction(formula, clause, remain, currentPigeon, knownPigeons, assigned, toAssign, watches)
                    currentPigeon.pop()
                    if knownPigeons != []:
                        break

# Build the candidates if we start the pigeon detection from a specific clause and launch the detection
def pigeonHoleDetection(formula, indClause, knownPigeons, blocked, assigned, toAssign, watches, marksLiterals):
    # Get the marks of the literals according to the starting clause
    marksLiterals = analyseClause(formula, indClause, assigned, toAssign, watches, marksLiterals)
    correspClauses = []
    cptCands = 0
    indexCands = []
    for indCand in range(len(formula)):
        if blocked[formula[indCand][0]] == 0 and len(formula[indCand][1]) == len(formula[indClause][1]):
            # Check if there is no common variable with the first clause
            common = False
            for candLit in formula[indCand][1]:
                if candLit in formula[indClause][1] or -candLit in formula[indClause][1]:
                    common = True
                    break
            if common is False:
                # Create the combinations
                marks = unitPropagationBitmask([marksLiterals[lit] for lit in formula[indCand][1]], -1, len(formula[indClause][1]))
                if marks != []:
                    combis = combinations(formula[indClause], marks, [])
                    # Reorder the literals for each combination
                    if len(combis) > 0:
                        cptCands += 1
                        indexCands.append(formula[indCand][0])
                        reorder = [deepcopy(formula[indCand]) for _ in range(len(combis))]
                        for ind in range(len(reorder)):
                            cl = reorder[ind][1].copy()
                            reorder[ind][1].sort(key=(lambda x : combis[ind][cl.index(x)]))
                        correspClauses += reorder
    #Try to construct pigeon hole problems if we have enough candidates
    if cptCands + 1 > len(formula[indClause][1]):
        pigeonHoleConstruction(formula, formula[indClause], correspClauses, [formula[indClause]], knownPigeons, assigned, toAssign, watches)


############################################ DPLL ###############################################


# Chose the next variable (next decision)
def choseNextVariable(assigned, heuris):
    if heuris != []:
        # Next decision if we consider the heuristic
        return heuris.pop(0)
    for i in range(1, nVariables + 1):
        # Chose the first free variable
        if assigned[i] == 0 and assigned[-i] == 0:
            return i
    return None

# Perform the pigeon hole detection on each clause we have to consider
def pigeonPur(formula, consider, assigned, toAssign, watches, marksLiterals, blocked):
    knownPigeons = []
    for ind in range(len(blocked)):
        blocked[ind] = 0
    for indClause in range(len(formula)):
        # We check if we have to consider the current clause
        # If it is the clause, we block it
        if consider[formula[indClause][0]]:
            blocked[formula[indClause][0]] = 1
            for ind in range(len(marksLiterals)):
                marksLiterals[ind] = 0
            # Begin the pigeon detection if the clause is of the correct size
            if len(formula[indClause][1]) >= minPigeons and len(formula[indClause][1]) <= maxPigeons:
                pigeonHoleDetection(formula, indClause, knownPigeons, blocked, assigned, toAssign, watches, marksLiterals)
                # If we have found a pigeon hole, we stop the function
                if knownPigeons != []:
                    break
    return knownPigeons

# Get the literals that have been assigned
def getAssignedLiterals(assigned):
    res = []
    for var in range(1, nVariables + 1):
        if assigned[var] == 1:
            res.append(var)
        elif assigned[-var] == 1:
            res.append(-var)
    return res

# Perform a DPLL search on the formula
def dpll(formula, nextPropagation, toPropagate, assigned, toAssign, decisions, level, heuris, toConsider, marksLiterals, blocked):
    # Reinitialize the values of the list of clauses to consider
    if nextPropagation != 0:
        for indClause in range(len(toConsider)):
            toConsider[indClause] = False
    # Propagate the new decision and simplify the formula
    ans, propagations, simpFormula = unitPropagation(formula, nextPropagation, toPropagate, [], -1, assigned, toAssign, watches, False, True, toConsider)
    if ans == "UNKNOWN":
        # Try to find pigeons
        pigeons = pigeonPur(simpFormula, toConsider, assigned, toAssign, watches, marksLiterals, blocked)
        if pigeons == []:
            # No pigeon hole has been detected
            print(decisions, "-> []\n")
        else:
            # Check if the detected pigeon is already known
            if str(pigeons[0]) not in known:
                # If it is not the case, we register it
                atleasts = len(pigeons[0])
                atmosts = len(pigeons[0][0][1])
                if (atleasts, atmosts) not in cptSize:
                    cptSize[(atleasts, atmosts)] = 0
                cptSize[(atleasts, atmosts)] += 1
                name = "ph" + str(atleasts) + "-" + str(atmosts) + "_" + str(cptSize[(atleasts, atmosts)])
                known[str(pigeons[0])] = name
            # Print the result of the search and unassign the propagated literals
            print(decisions, "->", known[str(pigeons[0])], "\n")
            assignedLiterals = getAssignedLiterals(assigned)
            undoPropagations(propagations, assigned, toAssign)
            return [["UNSAT", level, known[str(pigeons[0])], decisions.copy(), assignedLiterals]]
        # Chose the next variable
        nextVar = choseNextVariable(assigned, heuris)
        if nextVar is None:
            # SAT
            assignedLiterals = getAssignedLiterals(assigned)
            undoPropagations(propagations, assigned, toAssign)
            return [["SAT", assignedLiterals]]
        # First child (negative decision)
        decisions.append(-nextVar)
        toPropagate.append(-nextVar)
        answer1 = dpll(formula, -nextVar, toPropagate, assigned, toAssign, decisions, level + 1, heuris, toConsider, marksLiterals, blocked)
        decisions.pop()
        # Check if we have found an assignment with the first child
        lastAnswer = answer1[-1]
        if lastAnswer[0] == "SAT":
            undoPropagations(propagations, assigned, toAssign)
            return [lastAnswer]
        # Second child (positive decision)
        decisions.append(nextVar)
        toPropagate.append(nextVar)
        answer2 = dpll(formula, nextVar, toPropagate, assigned, toAssign, decisions, level + 1, heuris, toConsider, marksLiterals, blocked)
        decisions.pop()
        # Check if we have found an assignment with the second child
        lastAnswer = answer2[-1]
        if lastAnswer[0] == "SAT":
            undoPropagations(propagations, assigned, toAssign)
            return [lastAnswer]
        # Build the answer to the parent node
        answer1.extend(answer2)
        undoPropagations(propagations, assigned, toAssign)
        return answer1
    else:
        # UNSAT
        print(decisions, "-> UNSAT\n")
        assignedLiterals = getAssignedLiterals(assigned)
        undoPropagations(propagations, assigned, toAssign)
        return [["UNSAT", level, [], decisions.copy(), assignedLiterals]]


########################################## Handler ##############################################


# Print the detected pigeons if the SIGINT signal is received
def handler(signum, frame):
    print("\nDetected pigeons:")
    for pigeon in known:
        print("\n", known[pigeon], "=", pigeon)
    exit(1)


#################################################################################################
############################################ Main ###############################################
#################################################################################################


# parameters
if len(sys.argv) != 2:
	print("usage : python3 pigeonPur2.py instance.cnf")
	print("usage : ./pigeonPur2.py instance.cnf")
	exit(1)

# Expand recursion limit for some instances
sys.setrecursionlimit(10**6)

filename = sys.argv[1]

# Read the instance
file = open(filename, "r")
lines = file.readlines()
file.close()

# Get the formula
formula = []
toPropagate = []
cptClauses = -1
for line in lines:
    if line[0] == 'p':
        # Get the numbers of variables and clauses
        nVariables = int(line.split()[2])
        nClauses = int(line.split()[3])
        # We create some structures
        assigned = [0] * (2 * nVariables + 1)
        toAssign = [0] * (2 * nVariables + 1)
        marksLiterals = [0] * (2 * nVariables + 1)
        watches = [[] for _ in range(2 * nVariables + 1)]
        toConsider = [True] * nClauses
        blocked = [0] * nClauses
    elif line[0] != 'c':
        # We get a clause and add the corresponding watches
        clause = list(map(int, line.split()[0:-1]))
        if len(clause) == 1:
            # Binary clause
            assigned[clause[0]] = 1
            toPropagate.append(clause[0])
        elif clause != []:
            # Longer clause
            cptClauses += 1
            formula.append([cptClauses, clause])
            watchClause(watches, clause.copy())

# Parameters
maxPigeons = 64
minPigeons = 2
known = {}
cptSize = {}
heuristique = []
for ind in range(len(toConsider)):
    toConsider[ind] = True


# Define a handler for the SIGINT signal
signal.signal(signal.SIGINT, handler)

# Run the main programm
res = dpll(formula, 0, toPropagate, assigned, toAssign, [], 0, heuristique, toConsider, marksLiterals, blocked)

# Print the final result
print("\nFinal result:")
for r in res:
    print(r)

# print all the detected pigeons
print("\nDetected pigeons:")
for pigeon in known:
    print("\n", known[pigeon], "=", pigeon)

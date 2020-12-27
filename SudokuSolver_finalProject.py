import tkinter as tk

import itertools      
import re
import random
from functools import reduce
 

#%% Utilities
def first(iterable, default=None):
    """Return the first element of an iterable; or default."""
    return next(iter(iterable), default)

def count(seq):
    """Count the number of items in sequence that are interpreted as true."""
    return sum(map(bool, seq))

def argmin_random_tie(seq, key=lambda x: x):
    """Return a minimum element of seq; break ties at random."""
    items = list(seq)
    random.shuffle(items) #Randomly shuffle a copy of seq.
    return min(items, key=key)

def flatten(seqs):
    return sum(seqs, [])

def different_values_constraint(A, a, B, b):
    """A constraint saying two neighboring variables must differ in value."""
    return a != b


#%% CSP
class CSP():
    """This class describes finite-domain Constraint Satisfaction Problems.
    A CSP is specified by the following inputs:
        variables   A list of variables; each is atomic (e.g. int or string).
        domains     A dict of {var:[possible_value, ...]} entries.
        neighbors   A dict of {var:[var,...]} that for each variable lists
                    the other variables that participate in constraints.
        constraints A function f(A, a, B, b) that returns true if neighbors
                    A, B satisfy the constraint when they have values A=a, B=b
    """
    def __init__(self, variables, domains, neighbors, constraints):
        """Construct a CSP problem. If variables is empty, it becomes domains.keys()."""
        variables = variables or list(domains.keys())
        self.variables = variables
        self.domains = domains
        self.neighbors = neighbors
        self.constraints = constraints
        self.curr_domains = None
        self.nassigns = 0

    def assign(self, var, val, assignment):
        """Add {var: val} to assignment; Discard the old value if any."""
        assignment[var] = val
        self.nassigns += 1
        return assignment

    def unassign(self, var, assignment):
        """Remove {var: val} from assignment.
        DO NOT call this if you are changing a variable to a new value;
        just call assign for that."""
        if var in assignment:
            del assignment[var]

    def nconflicts(self, var, val, assignment):
        """Return the number of conflicts var=val has with other variables."""  
        # Subclasses may implement this more efficiently
        def conflict(var2):
            return var2 in assignment and not self.constraints(var, val, var2, assignment[var2])

        return count(conflict(v) for v in self.neighbors[var])


#%% Sudoku problem
# Constants and delarations to display and work with Sudoku grid
_R3 = list(range(3))
_CELL = itertools.count().__next__
_BGRID = [[[[_CELL() for x in _R3] for y in _R3] for bx in _R3] for by in _R3]
_BOXES = flatten([list(map(flatten, brow)) for brow in _BGRID])
_ROWS = flatten([list(map(flatten, zip(*brow))) for brow in _BGRID])
_COLS = list(zip(*_ROWS))
_NEIGHBORS = {v: set() for v in flatten(_ROWS)}
for unit in map(set, _BOXES + _ROWS + _COLS):
    for v in unit:
        _NEIGHBORS[v].update(unit - {v})


class Sudoku(CSP):
    """
    A Sudoku problem.
    init_assignment is a string of 81 digits for 81 cells, row by row.  
    Each filled cell holds a digit in 1..9. Each empty cell holds 0 or '.' 
    
    For example, for the below Sodoku
    init_assignment = '..3.2.6..9..3.5..1..18.64....81.29..7.......8..67.82....26.95..8..2.3..9..5.1.3..'"""
    R3 = _R3
    Cell = _CELL
    bgrid = _BGRID
    boxes = _BOXES
    rows = _ROWS
    cols = _COLS
    neighbors = _NEIGHBORS    
   
    def __init__(self, grid):
        """Build a Sudoku problem from a string representing the grid:
        the digits 1-9 denote a filled cell, '.' or '0' an empty one;
        other characters are ignored."""
        
        squares = re.findall(r'\d|\.', grid)            

        # NOTE: For variables in order of in order of 3x3 BOXES:
        domains = {var: list(ch) if ch in '123456789' else list('123456789')
                   for var, ch in zip(flatten(self.rows), squares)} #
        
        if len(squares) > 81:
            raise ValueError("Not a Sudoku grid", grid)  # Too many squares

        # For variables in order of in order of 3x3 BOXES:
        neighbors = {0: {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 18, 19, 20, 27, 30, 33, 54, 57, 60}, 1: {0, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 18, 19, 20, 28, 31, 34, 55, 58, 61}, 2: {0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 18, 19, 20, 29, 32, 35, 56, 59, 62}, 9: {0, 1, 2, 66, 69, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 36, 39, 42, 63}, 10: {0, 1, 2, 64, 67, 70, 9, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 37, 40, 43}, 11: {0, 1, 2, 65, 68, 71, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 38, 41, 44}, 18: {0, 1, 2, 72, 9, 10, 11, 75, 78, 19, 20, 21, 22, 23, 24, 25, 26, 45, 48, 51}, 19: {0, 1, 2, 9, 10, 11, 73, 76, 79, 18, 20, 21, 22, 23, 24, 25, 26, 46, 49, 52}, 20: {0, 1, 2, 9, 10, 11, 74, 77, 80, 18, 19, 21, 22, 23, 24, 25, 26, 47, 50, 53}, 3: {0, 1, 2, 4, 5, 6, 7, 8, 12, 13, 14, 21, 22, 23, 27, 30, 33, 54, 57, 60}, 4: {0, 1, 2, 3, 5, 6, 7, 8, 12, 13, 14, 21, 22, 23, 28, 31, 34, 55, 58, 61}, 5: {0, 1, 2, 3, 4, 6, 7, 8, 12, 13, 14, 21, 22, 23, 29, 32, 35, 56, 59, 62}, 12: {66, 3, 4, 5, 69, 9, 10, 11, 13, 14, 15, 16, 17, 21, 22, 23, 36, 39, 42, 63}, 13: {64, 3, 4, 5, 67, 70, 9, 10, 11, 12, 14, 15, 16, 17, 21, 22, 23, 37, 40, 43}, 14: {65, 3, 4, 5, 68, 71, 9, 10, 11, 12, 13, 15, 16, 17, 21, 22, 23, 38, 41, 44}, 21: {3, 4, 5, 72, 75, 12, 13, 14, 78, 18, 19, 20, 22, 23, 24, 25, 26, 45, 48, 51}, 22: {3, 4, 5, 73, 12, 13, 14, 76, 79, 18, 19, 20, 21, 23, 24, 25, 26, 46, 49, 52}, 23: {3, 4, 5, 74, 12, 13, 14, 77, 80, 18, 19, 20, 21, 22, 24, 25, 26, 47, 50, 53}, 6: {0, 1, 2, 3, 4, 5, 7, 8, 15, 16, 17, 24, 25, 26, 27, 30, 33, 54, 57, 60}, 7: {0, 1, 2, 3, 4, 5, 6, 8, 15, 16, 17, 24, 25, 26, 28, 31, 34, 55, 58, 61}, 8: {0, 1, 2, 3, 4, 5, 6, 7, 15, 16, 17, 24, 25, 26, 29, 32, 35, 56, 59, 62}, 15: {66, 69, 6, 7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 24, 25, 26, 36, 39, 42, 63}, 16: {64, 67, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 17, 24, 25, 26, 70, 37, 40, 43}, 17: {65, 68, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 24, 25, 26, 38, 71, 41, 44}, 24: {6, 7, 8, 72, 75, 78, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 26, 45, 48, 51}, 25: {6, 7, 8, 73, 76, 79, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 26, 46, 49, 52}, 26: {6, 7, 8, 74, 77, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 80, 47, 50, 53}, 27: {0, 3, 6, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 45, 46, 47, 54, 57, 60}, 28: {1, 4, 7, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 45, 46, 47, 55, 58, 61}, 29: {2, 5, 8, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 45, 46, 47, 56, 59, 62}, 36: {66, 69, 9, 12, 15, 27, 28, 29, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 63}, 37: {64, 67, 70, 10, 13, 16, 27, 28, 29, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47}, 38: {65, 68, 71, 11, 14, 17, 27, 28, 29, 36, 37, 39, 40, 41, 42, 43, 44, 45, 46, 47}, 45: {72, 75, 78, 18, 21, 24, 27, 28, 29, 36, 37, 38, 46, 47, 48, 49, 50, 51, 52, 53}, 46: {73, 76, 79, 19, 22, 25, 27, 28, 29, 36, 37, 38, 45, 47, 48, 49, 50, 51, 52, 53}, 47: {74, 77, 80, 20, 23, 26, 27, 28, 29, 36, 37, 38, 45, 46, 48, 49, 50, 51, 52, 53}, 30: {0, 3, 6, 27, 28, 29, 31, 32, 33, 34, 35, 39, 40, 41, 48, 49, 50, 54, 57, 60}, 31: {1, 4, 7, 27, 28, 29, 30, 32, 33, 34, 35, 39, 40, 41, 48, 49, 50, 55, 58, 61}, 32: {2, 5, 8, 27, 28, 29, 30, 31, 33, 34, 35, 39, 40, 41, 48, 49, 50, 56, 59, 62}, 39: {66, 69, 9, 12, 15, 30, 31, 32, 36, 37, 38, 40, 41, 42, 43, 44, 48, 49, 50, 63}, 40: {64, 67, 70, 10, 13, 16, 30, 31, 32, 36, 37, 38, 39, 41, 42, 43, 44, 48, 49, 50}, 41: {65, 68, 71, 11, 14, 17, 30, 31, 32, 36, 37, 38, 39, 40, 42, 43, 44, 48, 49, 50}, 48: {72, 75, 78, 18, 21, 24, 30, 31, 32, 39, 40, 41, 45, 46, 47, 49, 50, 51, 52, 53}, 49: {73, 76, 79, 19, 22, 25, 30, 31, 32, 39, 40, 41, 45, 46, 47, 48, 50, 51, 52, 53}, 50: {74, 77, 80, 20, 23, 26, 30, 31, 32, 39, 40, 41, 45, 46, 47, 48, 49, 51, 52, 53}, 33: {0, 3, 6, 27, 28, 29, 30, 31, 32, 34, 35, 42, 43, 44, 51, 52, 53, 54, 57, 60}, 34: {1, 4, 7, 27, 28, 29, 30, 31, 32, 33, 35, 42, 43, 44, 51, 52, 53, 55, 58, 61}, 35: {2, 5, 8, 27, 28, 29, 30, 31, 32, 33, 34, 42, 43, 44, 51, 52, 53, 56, 59, 62}, 42: {66, 69, 9, 12, 15, 33, 34, 35, 36, 37, 38, 39, 40, 41, 43, 44, 51, 52, 53, 63}, 43: {64, 67, 70, 10, 13, 16, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 44, 51, 52, 53}, 44: {65, 68, 71, 11, 14, 17, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 51, 52, 53}, 51: {72, 75, 78, 18, 21, 24, 33, 34, 35, 42, 43, 44, 45, 46, 47, 48, 49, 50, 52, 53}, 52: {73, 76, 79, 19, 22, 25, 33, 34, 35, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 53}, 53: {74, 77, 80, 20, 23, 26, 33, 34, 35, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52}, 54: {64, 65, 0, 3, 6, 72, 73, 74, 27, 30, 33, 55, 56, 57, 58, 59, 60, 61, 62, 63}, 55: {64, 65, 1, 4, 7, 72, 73, 74, 28, 31, 34, 54, 56, 57, 58, 59, 60, 61, 62, 63}, 56: {64, 65, 2, 5, 72, 73, 74, 8, 29, 32, 35, 54, 55, 57, 58, 59, 60, 61, 62, 63}, 63: {64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 9, 12, 15, 36, 39, 42, 54, 55, 56}, 64: {65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 10, 13, 16, 37, 40, 43, 54, 55, 56, 63}, 65: {64, 66, 67, 68, 69, 70, 71, 72, 73, 74, 11, 14, 17, 38, 41, 44, 54, 55, 56, 63}, 72: {64, 65, 73, 74, 75, 76, 77, 78, 79, 80, 18, 21, 24, 45, 48, 51, 54, 55, 56, 63}, 73: {64, 65, 72, 74, 75, 76, 77, 78, 79, 80, 19, 22, 25, 46, 49, 52, 54, 55, 56, 63}, 74: {64, 65, 72, 73, 75, 76, 77, 78, 79, 80, 20, 23, 26, 47, 50, 53, 54, 55, 56, 63}, 57: {0, 66, 67, 68, 3, 6, 75, 76, 77, 27, 30, 33, 54, 55, 56, 58, 59, 60, 61, 62}, 58: {1, 66, 67, 68, 4, 7, 75, 76, 77, 28, 31, 34, 54, 55, 56, 57, 59, 60, 61, 62}, 59: {66, 67, 68, 2, 5, 8, 75, 76, 77, 29, 32, 35, 54, 55, 56, 57, 58, 60, 61, 62}, 66: {64, 65, 67, 68, 69, 70, 71, 9, 75, 76, 77, 12, 15, 36, 39, 42, 57, 58, 59, 63}, 67: {64, 65, 66, 68, 69, 70, 71, 10, 75, 76, 77, 13, 16, 37, 40, 43, 57, 58, 59, 63}, 68: {64, 65, 66, 67, 69, 70, 71, 75, 76, 77, 11, 14, 17, 38, 41, 44, 57, 58, 59, 63}, 75: {66, 67, 68, 72, 73, 74, 76, 77, 78, 79, 80, 18, 21, 24, 45, 48, 51, 57, 58, 59}, 76: {66, 67, 68, 72, 73, 74, 75, 77, 78, 79, 80, 19, 22, 25, 46, 49, 52, 57, 58, 59}, 77: {66, 67, 68, 72, 73, 74, 75, 76, 78, 79, 80, 20, 23, 26, 47, 50, 53, 57, 58, 59}, 60: {0, 3, 69, 70, 71, 6, 78, 79, 80, 27, 30, 33, 54, 55, 56, 57, 58, 59, 61, 62}, 61: {1, 4, 69, 70, 71, 7, 78, 79, 80, 28, 31, 34, 54, 55, 56, 57, 58, 59, 60, 62}, 62: {2, 69, 70, 71, 5, 8, 78, 79, 80, 29, 32, 35, 54, 55, 56, 57, 58, 59, 60, 61}, 69: {64, 65, 66, 67, 68, 70, 71, 9, 12, 78, 79, 80, 15, 36, 39, 42, 60, 61, 62, 63}, 70: {64, 65, 66, 67, 68, 69, 71, 10, 13, 78, 79, 80, 16, 37, 40, 43, 60, 61, 62, 63}, 71: {64, 65, 66, 67, 68, 69, 70, 11, 78, 79, 80, 14, 17, 38, 41, 44, 60, 61, 62, 63}, 78: {69, 70, 71, 72, 73, 74, 75, 76, 77, 79, 80, 18, 21, 24, 45, 48, 51, 60, 61, 62}, 79: {69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 80, 19, 22, 25, 46, 49, 52, 60, 61, 62}, 80: {69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 20, 23, 26, 47, 50, 53, 60, 61, 62}}
        
        CSP.__init__(self, list(domains.keys()), domains, neighbors, different_values_constraint)

    def display(self): # For variables in order of in order of 3x3 BOXES
        """Show a human-readable representation of the Sudoku."""
        place = 0
        if self.curr_domains is not None:
            self.domains = self.curr_domains.copy() 
        for var in self.domains.keys():
            if place%3 == 0 and place%9 != 0 :
                print('  |', end = '')
            if place%9 == 0 and place!=0:
                print('')
            if place%27 == 0 and place!=0:
                print(' --------------------------------')

            if len(self.domains[var])==1:
                print('%3s' % self.domains[var][0], end = '')
            else:
                print('  .', end = '')  
            place += 1
        print('\n')    
         
    def display_variables(self): # For variables in order of in order of 3x3 BOXES
        place = 0
        for var in self.domains.keys():
            if place%3 == 0 and place%9 != 0 :
                print('  |', end = '')
            if place%9 == 0 and place!=0:
                print('')
            if place%27 == 0 and place!=0:
                print(' --------------------------------')

            print('%3s' % var, end = '')
            
            place += 1
        print('\n')     
#%%  CSP Backtracking Search  
# Variable ordering
def first_unassigned_variable(assignment, csp): #random selection
    """The default variable order."""
    return first([var for var in csp.variables if var not in assignment])

def num_legal_values(csp, var, assignment):
    if csp.curr_domains:
        return len(csp.curr_domains[var])
    else:
        return count(csp.nconflicts(var, val, assignment) == 0 for val in csp.domains[var])

def minimum_remaining_values(assignment, csp):
    """Minimum-remaining-values heuristic."""
    return argmin_random_tie([v for v in csp.variables if v not in assignment],
                             key=lambda var: num_legal_values(csp, var, assignment))

# Value ordering
def unordered_domain_values(var, assignment, csp): #random selection
    """The default value order."""
    return (csp.curr_domains or csp.domains)[var]

def least_constraining_value(var, assignment, csp):
    """Least-constraining-values heuristic."""
    return sorted((csp.curr_domains or csp.domains)[var], key=lambda val: csp.nconflicts(var, val, assignment))   

# Inference
def forward_checking(csp, var, value, assignment, removals):
    """Prune neighbor values inconsistent with var=value."""
    for B in csp.neighbors[var]:
        if B not in assignment:
            for b in csp.curr_domains[B][:]:
                if not csp.constraints(var, value, B, b):
                    csp.curr_domains[B].remove(b)
                    if removals is not None:
                        removals.append((B, b)) # variable B and value b are removed from its domain
            if not csp.curr_domains[B]:
                return False
    return True
 

''' READ AND COMMENT to show your comprehensive understanding of the following function '''
# Backtracking search
def backtracking_search(csp, select_unassigned_variable=minimum_remaining_values,
                        order_domain_values=least_constraining_value, 
                        inference=forward_checking):
    """See [Figure 6.5] for the algorithm"""       
    def backtrack(assignment):            
        if len(assignment) == len(csp.variables):
            return assignment
        # choose variable with the fewest "legal" value
        var = select_unassigned_variable(assignment, csp)

        # choose the value that have the least affect on other variable's domain
        for value in order_domain_values(var, assignment, csp):

            # check if selected value is satisfies the contraint
            if 0 == csp.nconflicts(var, value, assignment):

                # add variable and its value to assignment
                csp.assign(var, value, assignment)
                
                # list of variable which domain will be reduced in inference function
                removals = [(var, a) for a in csp.curr_domains[var] if a != value] 

                csp.curr_domains[var] = [value]  
                

                # check if assigned value is consistent and remove it from other variable's domain
                if inference(csp, var, value, assignment, removals):

                    # if true continue
                    result = backtrack(assignment)

                    # find result
                    if result is not None:
                        return result        
                # restore other variable's domain
                restore(csp, removals)  
        
        # remove variable from assignment
        csp.unassign(var, assignment) 
        #print("Running")
        return None

    csp.curr_domains = csp.domains.copy()

    # Start
    result = backtrack({})       
    
    return result

def restore(csp, removals):
    """Undo a supposition and all inferences from it."""
    for B, b in removals:
        csp.curr_domains[B].append(b)


# Global Matrix where are stored the numbers
window= tk.Tk()
# window.resizable(False,False)
savedNumbers = []
for i in range(1,10):
    savedNumbers += [[0,0,0,0,0,0,0,0,0]]
for i in range(0,9):
    for j in range(0,9):
        savedNumbers[i][j] = tk.StringVar(window,value='')


# create widget and stuff
class gameLauncher():
    
    def __init__(self,window):
        # set window title
        window.title('sudoku solver v1.0')
        self.flag=False
        # set some usefull variable
        self.font = ('Calibri 15 bold')
        color = 'white'
        statusfrm=tk.Frame(window)
        # create status 
        self.statusLabel=tk.Label(statusfrm,justify=tk.CENTER,width=5,font=self.font,fg='#ffffff',bg='#007acc')
        
        # # insert text to entry, this entry will be updated when program is solving sudoku
        self.statusLabel['text']='welcome'
        
        # # dock status on top
        self.statusLabel.pack(side=tk.TOP,fill=tk.X)
        statusfrm.pack(fill=tk.X)
        frm=tk.Frame(window)
        frm.pack(side=tk.TOP)
        

        # valid row
        self.row=[]
        for i in range(1,10):
            self.row+=[set()]
        # valid col
        self.col=[]
        for i in range(1,10):
            self.col+=[set()]
        
        # valid block
        self.block=[]
        for i in range(1,10):
            self.block+=[set()]

        # create grid 
        # create list to track entry 
        self.track = []
        for i in range(1,10):
            self.track += [[0,0,0,0,0,0,0,0,0]]

        window.columnconfigure(8,weight=1)

        # cell validation
        for i in range(0,9):
            for j in range(0,9):
                
                if (i < 3 or i > 5) and (j < 3 or j > 5):
                    color = '#070707'
                elif i in [3,4,5] and j in [3,4,5]:
                    color = '#070707'
                else:
                    color = '#161514'
                self.track[i][j] = tk.Entry(frm,width=5,bg = color, cursor = 'arrow', borderwidth = 0,font=self.font,justify=tk.CENTER,
                                          highlightcolor = '#ffb900', highlightthickness = 1, highlightbackground = '#222323',
                                          textvar = savedNumbers[i][j],fg='#ffffff',insertbackground='#ffffff')
                # self.track[i][j].bind('<Motion>', self.correctGrid)
                # self.track[i][j].bind('<FocusIn>', self.correctGrid)
                self.track[i][j].bind('<FocusOut>', self.correctGrid)

                self.track[i][j].bind('<Button-1>', self.correctGrid)
                self.track[i][j].grid(row=i, column=j,ipady=14)
        # menu
        menu=tk.Menu(window)
        window.config(menu=menu)
        file=tk.Menu(menu,tearoff=0)
        menu.add_cascade(label='File',menu=file)
        file.add_command(label='solve',command=self.solver)
        file.add_command(label='clear',command=self.clear)
        help=tk.Menu(menu,tearoff=0)

        menu.add_cascade(label='Help',menu=help)

        help.add_command(label='About',command=self.help)

    # help button
    def help(self):
        font = ('Calibri 12 bold')

        newWindow = tk.Toplevel(window) 
        about=tk.Text(newWindow,width=100,wrap=tk.WORD,font=font)
        about.insert(0.0,'This sudoku solver program use backtracking algorithm to find solution. Enter the numbers of the puzzle you want to solve in the grid, click File > sovle; the program will give you a solution. If you want to start again, click File > clear, the program will clear the grid for you. It also support input validation, you can solve the puzzle by yourself. The cell\'s text will turn red if you input the wrong number, otherwise, it is green.')
        about.pack(fill=tk.BOTH,expand=tk.TRUE,padx=5,pady=5,ipadx=10,ipady=10)

    def correctGrid(self, event):
        widget=event.widget
        i,j=widget.grid_info()['row'],widget.grid_info()['column']

        # set flag, prevent edit cell
        if self.flag==True:
            return
        # input validation
        if savedNumbers[i][j].get()=='':
            return
        if savedNumbers[i][j].get() not in ['1','2','3','4','5','6','7','8','9']:
            savedNumbers[i][j].set('')
            return
        blockIndex=(i // 3 ) * 3 + j // 3
        # check col, row, and block
        if savedNumbers[i][j].get() not in self.row[i] and savedNumbers[i][j].get() not in self.col[j] and savedNumbers[i][j].get() not in self.block[blockIndex]:
            widget.configure(fg='#7fba00')
            self.row[i].add(savedNumbers[i][j].get())
            self.col[j].add(savedNumbers[i][j].get())
            self.block[blockIndex].add(savedNumbers[i][j].get())
            return
        if ( savedNumbers[i][j].get() in self.row[i] or savedNumbers[i][j].get() in self.col[j] or savedNumbers[i][j].get() in self.block[blockIndex]):
            # savedNumbers[i][j].set('')
            widget.configure(fg='#f25022')
        
    # clear grid
    def clear(self):
        for i in range(9):
            for j in range(9):
                savedNumbers[i][j].set('')
                self.track[i][j].configure(fg='#ffffff')
        # clear row, col, and block check
        for i in range(9):
            self.row[i]=set()
            self.col[i]=set()
            self.block[i]=set()
        self.flag=False
        self.statusLabel['text']='Welcome back :)'
    
    # solve puzzle
    def solver(self):
        if self.flag==True:
            self.statusLabel['text']='Please, clear the grid :('
            return
        # parse input to problem
        input=''
        for i in range(9):
            for j in range(9):
                if(savedNumbers[i][j].get()!=''):
                    input+=savedNumbers[i][j].get()
                else:
                    input+='.'
        # call backtracking function
        init_assign_hard = input
        sodoku = Sudoku(init_assign_hard)
        backtracking_search(sodoku)

        # get result and put to string
        resultConvert=''
        for x in sodoku.domains:
            resultConvert+=sodoku.domains[x][0]
        count=0
        # count # of 1
        checkValidInput=0

        # catch wrong solution
        for i in range(81):
            if sodoku.domains[i][0]=='1':
                checkValidInput+=1
            if checkValidInput==10:
                self.statusLabel['text']=':( invalid input!! Please try again'
                return
        
        self.statusLabel['text']=':) solving, please wait'
        self.statusLabel.update()
        for i in range(9):
            for j in range(9):
                savedNumbers[i][j].set(resultConvert[count])
                self.track[i][j].configure(fg='#ffffff')
                count+=1
        self.statusLabel['text']=':) solved'
        self.flag=True
        # print(sodoku.domains)

        

# launch game
gameLauncher(window)
print(window.winfo_width())
window.mainloop()
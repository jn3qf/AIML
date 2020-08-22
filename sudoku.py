# SUDOKU (TJ AI 1), JEREMY NATHAN // MAY 2020
from timeit import default_timer as timer
from itertools import chain, combinations
from multiprocessing import Pool, cpu_count
import sys

class Board():
    def __init__(self, inputstring: str):

        self.N = int(len(inputstring) ** (1/2))
        self.matrix = list(inputstring)

        factors = [(i, int(self.N/i)) for i in range(1, int(self.N**(1/2) + 1)) if self.N % i == 0]
        self.H, self.W = factors[-1]
        self.sym_set = '123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ'[:self.N]

        #constraints[0]: row constraints
        constraints = [{i: [(i*self.N + y) for y in range(self.N)] for i in range(self.N)}]
        #constraints[1]: column constraints
        constraints += [{j: [(x*self.N + j) for x in range(self.N)] for j in range(self.N)}]
        #constraints[2]: block constraints
        constraints += [{}]
        for x in range(0, self.N, self.H):
            for y in range(0, self.N, self.W):
                blk = []
                for i in range(x, x + self.H):
                    for j in range(y, y + self.W):
                        blk.append(i*self.N + j)
                constraints[2][(int(x/self.H), int(y/self.W))] = blk

        self.neighbors = [ [] for i in range(0, self.N**2) ]

        for i in range(self.N):
            for j in range(self.N):
                #add row constraint, exclude self
                neighbors = [val for val in constraints[0][i] if val != i*self.N + j]
                #add column constraint, exclude self
                neighbors += [val for val in constraints[1][j] if val != i*self.N + j]
                #add block constraint, exclude self
                neighbors += [val for val in constraints[2][int(i / self.H), int(j / self.W)]
                                if val != i*self.N + j and val not in neighbors]
                #add the constraints for this i,j to the matrix
                self.neighbors[i*self.N + j] = neighbors
        
        self.constraints = list(chain.from_iterable([l.values() for l in constraints]))


    def __str__(self):
        return ''.join(self.matrix)
    
    
    def grid_view(self):
        formattedmatrix = []
        for i in range(self.N):
            newline = []
            for j in range(0, self.N, self.W):
                newline += self.matrix[i*self.N + j: i*self.N + j + self.W]
                if j < self.N - self.W:
                    newline += ['|']
            formattedmatrix += [newline]
            if (i + 1) % self.H == 0 and 0 < i < self.N - 1:
                formattedmatrix += [['-']*(int(self.N + self.N/self.W) - 1)]
        return ''.join([' '.join(line) + '\n' for line in formattedmatrix])


    def solve(self):

        def check(state: list):
            tallies = {k: 0 for k in self.sym_set}
            for i in state:
                if i != '.':
                    tallies[i] += 1
            return all([tallies[key] == self.N for key in tallies])


        def initialize_poss(state: list):
            possibilities = {}
            solved_indices = set()
            for i in range(self.N**2):
                if state[i] == '.':
                    poss_values = set(self.sym_set)
                    for neighbor_loc in self.neighbors[i]:
                        value_to_remove = state[neighbor_loc]
                        if value_to_remove != '.' and value_to_remove in poss_values:
                            poss_values.remove(state[neighbor_loc])
                    if len(poss_values) == 1:
                        solved_indices.add(i)
                    possibilities[i] = poss_values
            return possibilities, solved_indices

        # given the state, possibilities for each index, and the list of newly solved indices,
        # iterate until there are no indices with one possibility left.
        def forward_look(state: list, poss: dict, newly_solved_indices: set):
            while newly_solved_indices:
                # get the solved index and its value from the queue
                solved_index = newly_solved_indices.pop()
                # get and remove the solved index from dict of possibilities
                solved_value = poss.pop(solved_index).pop()
                # set the solved index of the state to the solved value
                state[solved_index] = solved_value
                # remove the solved value from the solved index's neighbors possible values
                for neighboring_index in self.neighbors[solved_index]:
                    if neighboring_index in poss and solved_value in poss[neighboring_index]:
                        poss[neighboring_index].remove(solved_value)
                        # if this was the only possible value for another neighbor, return failure
                        if len(poss[neighboring_index]) == 0:
                            return None, None
                        # else, if the other neighbor now only has one possible value, add it to the queue
                        if len(poss[neighboring_index]) == 1:
                            newly_solved_indices.add(neighboring_index)

            return propagate_constraints(state, poss)


        def propagate_constraints(state: list, poss: dict):
            newly_solved_indices = set()
            for constraint in self.constraints:
                #set up a dictionary containing the set of indices for which each possible value appears
                value_dict = {k: set() for k in self.sym_set}
                #set up a list of indices in the constraint.
                locs_to_check = list(constraint)
                #set up a reverse dictionary containing the possible values for each index in the constraint
                reverse_value_dict = {c: set() for c in locs_to_check}

                for var in constraint:
                    # if the index is solved,
                    if var not in poss:
                        # remove the solved value from value_dict.
                        value_dict.pop(state[var])
                        # remove the index from locs_to_check and from reverse_value_dict
                        locs_to_check.remove(var)
                        reverse_value_dict.pop(var)
                    else:
                        # if the index is unsolved, copy possible values into reverse dict
                        reverse_value_dict[var] = set(poss[var])

                # optimization 1. If N squares in the set have the exact same set of N possible values,
                # only these squares can have those values. Remove those N values from any other squares in the constraint.
                for i, var in enumerate(locs_to_check):
                    equals = {var}
                    for comp_var in locs_to_check[i+1:]:
                        if len(poss[var]) > 1 and poss[var] == poss[comp_var]:
                            equals.add(comp_var)

                    if len(equals) == len(poss[var]):
                        locs_to_mod = set(locs_to_check) - equals
                        for loc in locs_to_mod:
                            poss[loc] -=  poss[var]
                            reverse_value_dict[loc] = set(poss[loc])
                            if len(poss[loc]) == 0:
                                return None, None
                            if len(poss[loc]) == 1:
                                newly_solved_indices.add(loc)
                    # if more than N squares have the N values (i.e. 3 squares have the possible values [2,7]), return failure.
                    elif len(equals) > len(poss[var]):
                        return None, None

                    for k in value_dict:
                        if k in poss[var]:
                            value_dict[k].add(var)


                # optimization 2. If a subset of possible values S for a given index only appears in |S| indices, 
                # those indices can only contain values in S.
                reverse_value_dict_keys = set(reverse_value_dict.keys())
                while reverse_value_dict:
                    var = reverse_value_dict_keys.pop()
                    values = reverse_value_dict.pop(var)
                    # generate all possible subsets for this index.
                    valid_set = list(chain.from_iterable([combinations(values,r) for r in range(2, len(values) + 1)]))
                    found = False
                    # examine each subset as long as a subset satisfying the condition hasn't been found for this index.
                    while valid_set and not found:
                        value_subset = valid_set.pop(0)
                        equals = value_dict[value_subset[0]]
                        if len(equals) != len(value_subset):
                            continue
                        found = True
                        for k in value_subset[1:]:
                            if value_dict[k] != equals:
                                found = False
                                break
                        if found:
                            for loc in equals:
                                poss[loc] = set(value_subset)
                                if loc in reverse_value_dict:
                                    reverse_value_dict.pop(loc)
                                    reverse_value_dict_keys.remove(loc)
                                for k in value_dict:
                                    if loc in value_dict[k] and k not in value_subset:
                                        value_dict[k].remove(loc)
                            for k in value_subset:
                                value_dict[k] = set(value_subset)

                    # All the values in the subsets checked either were part of a subset that
                    # fulfilled the condition, or not. Regardless, the values checked will never be part of a future subset
                    # that fulfills the condition, so we can remove these possible values from each index to check.
                    for loc in reverse_value_dict:
                        reverse_value_dict[loc] -= values


                for k in value_dict:                       
                    if len(value_dict[k]) == 0:
                        return None, None
                    if len(value_dict[k]) == 1:
                        new_index = value_dict[k].pop()
                        newly_solved_indices.add(new_index)
                        poss[new_index] = {k}
            
            # if this method found new indices that are solved, call FL method again for new indices.
            if newly_solved_indices:
                state, poss = forward_look(state, poss, newly_solved_indices)

            return state, poss


        def csp_backtracking(state: list, poss: list):
            if check(state):
                return state
            
            var = min(poss, key=lambda s: len(poss[s]))
            poss_values = poss[var]

            for val in poss_values:
                #create a new state, replacing index var with the test value
                new_state = list(state)
                new_state[var] = val
                
                #create a new list of possibilities. For the var index we just 'solved',
                #the test value we put in should be the only possibility.
                new_poss = {key: set(poss[key]) if key != var else {val} for key in poss}
                checked_board, checked_poss = forward_look(new_state, new_poss, {var})

                if checked_board is not None:
                    result = csp_backtracking(checked_board, checked_poss)
                    if result is not None:
                        return result
            return None

        possibilities, newly_solved_indices = initialize_poss(self.matrix)
        state, poss = forward_look(self.matrix, possibilities, newly_solved_indices)
        self.matrix = csp_backtracking(state, poss)


def readFromFile(file: str):
    with open(file) as f:
        return [(i, Board(line.strip())) for i, line in enumerate(f)]


def solve_and_store(i, puzzle):
    original = str(puzzle)
    print(f'SOLVING PUZZLE {i+1}...')
    start = timer()
    puzzle.solve()
    end = timer()
    solved = puzzle.grid_view()
    time_taken = end-start
    print(f'PUZZLE {i+1} SOLVED IN {time_taken:2.3e} S.', flush=True)
    return (i+1, original, solved, time_taken)


if __name__ == "__main__":
    puzzles = readFromFile(filename := sys.argv[1])
    
    with Pool(cpu_count()) as p:
        overall_start = timer()
        solution_times = p.starmap(solve_and_store, puzzles)
        overall_end = timer()

    list.sort(solution_times, key = lambda s: s[0])
    print('>> SOLUTIONS')
    for i, orig, solved, _ in solution_times:
        print(f'> PUZZLE {i}:')
        print(orig)
        print(solved)

    list.sort(solution_times, key = lambda s: s[3])
    print('>> INDIVIDUAL TIMINGS (S)')
    for i, _, _, t in solution_times:
        print(f'{i}\t{t:1.2e}')

    print(f'{len(puzzles)} PUZZLES IN {filename} SOLVED IN {(overall_end - overall_start):4.2f} SECONDS')
This SAT_solver has been written by Udayan Joshi and Divya Raghunathan, as part of the final course project for CS154 lab.

The Solver is completely written in racket.
All the code is written using the Functional Programming as a paradigm.
The implementation is in the file sat_solver.rkt
We have implemented the basic backtracking search, DPLL algorithm with simple branching as well as DPLL with a DLIS(Dynamic Largest Individual Sum) heuristic.


The code is run by giving the command
(main)

This displays a list of problems that can be solved. On entering the corresponding number, a list of algorithms that can be used will be displayed.

If satisfiability is chosen, run the command
(solve F)
F is the formula in CNF, written as a list of lists. A negative literal is denoted by -x, where x is a variable. For example, '((x y) (-x)) denotes the formula (x or y) and (not x).

If four queens or eight queens is chosen, the result will be displayed, as a configuration of the board. 'Q' denotes that the square is occupied by a queen, '-' denotes an empty square.

If Sudoku is chosen, a Sudoku puzzle must be entered, one row at a time. A row must be of the form "xyzw" where each x, y, z, w are either numbers from 1 to 4 or '.', which denotes an empty square.

At the end there is an option to continue or to exit.


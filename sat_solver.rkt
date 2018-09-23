#lang racket

(require data/gvector)
(require "4queens.rkt")
(require "4sudoku.rkt")
(require "8queens.rkt")

(define CNF_formula (make-gvector)) ; formula, stored as a gvector of clauses, clause: list of literals
(define init-assignment (make-hash)) ; stores the initial assignment (all 0)
(define lit-weights (make-hash)) ; DLIS weights of each literal.
                                 ; key- pair of variable name and polarity, value- number of clauses that contain that literal

(define opcode -1)  ; code denoting which problem is currently being solved. 0 : SAT, 1 : four queens, 2 : 4 X 4 sudoku, 3 : Eight queens
(define method-code -1)  ; denotes the search method being used. 0 : backtrack, 1: dpll, 2: dpll-dlis


;; class representing a literal

(define literal%
  (class object%
    (init-field sym)
    (init-field polarity)
    (super-new)
    (define/public (show) (list sym polarity))
    ))

                  
;; simplification of formula F under a given assignment
(define (simplify F assignment flag)
  ; F is a gvector of lists of literals
  ; flag: indicates the DPLL variant. 0: simple branching heuristic, 1: DLIS heuristic
  
  (define (assign literal-list assignment) ; assigns literals in the given clause (literal-list)
    (define (assign-helper i res)
      (if (= i (length literal-list)) res
          (let*[(el (list-ref literal-list i))
                (el-assign (hash-ref assignment (symbol->string (get-field sym el)) (lambda () (begin (display (get-field sym el)) (error "key not found")))))]
            (if (not (boolean? el-assign)) (assign-helper (+ i 1) res) ; not assigning el
                (if (= (get-field polarity el) 1)
                    (if (equal? el-assign #t) (cond [(= flag 1) (begin (weights-remove-clause literal-list) #t)] ; clause 'literal-list' becomes #t
                                                    [else #t])
                        (assign-helper (+ i 1) (list-set res i #f)))
                    (if (equal? el-assign #t) (assign-helper (+ i 1) (list-set res i #f))
                        (cond [(= flag 1) (begin (weights-remove-clause literal-list) #t)] ; clause 'literal-list' becomes #t
                              [else #t])))))))
    (if (equal? literal-list #t) #t
        (assign-helper 0 literal-list)))

  (define (simplify-clause cl) ; simplifies clause cl. If cl contains #t, cl simplifies to #t. If cl contains #f, the #f can be removed.
    (if (equal? cl #t) #t
        (let* [(temp-list (assign cl assignment))
               (assigned-list (cond [(equal? temp-list #t) #t]
                                    [else (let [(filtered_list (filter (lambda (x) (not (equal? x #f))) temp-list))]
                                            (if (null? filtered_list) #f
                                                filtered_list))]))]
          assigned-list)))

  (define (simplify-helper i) ; iterates through the clauses of formula. Returns formula with each clause simplified.
    (if (= i (gvector-count F)) res
        (let* [(cl (gvector-ref F i))
               (simp-cl (simplify-clause cl))]
          (begin (gvector-set! res i simp-cl)
                 (simplify-helper (+ i 1))))))
  
  (define (simplify-and list-clauses) ; simplifies the formula with each clause already simplified. If a clause is #f, the formula evaluates to #f.
                                      ; If the formula contains #t, the #t can be removed.
    (define simp-clauses (remove* (list #t) list-clauses)) 
    (define (simplify-and-helper i)
      (if (= i (length simp-clauses)) simp-clauses
          (let* [(cl (list-ref simp-clauses i))]
            (if (equal? cl #f) #f ; clause is #f - not satisfiable
                (simplify-and-helper (+ i 1))))))
    (if (null? simp-clauses) #t
        (simplify-and-helper 0)))
  
  (define res (make-gvector))
  (simplify-helper 0)
  (define simp-expr (simplify-and (gvector->list res)))
  (if (boolean? simp-expr) simp-expr
      (list->gvector simp-expr)))

;; function which modifies DLIS weights during simplification of the formula
(define (weights-remove-clause cl)    ; modify lit-weights when clause cl is set to #t (when a clause is removed)
                                      ; decrement weight of all literals in cl
  (define len (length cl))
  (define (weights-remove-cl-helper i)
    (cond [(< i len)
           (begin (let* [(lit (list-ref cl i))
                         (var-name (symbol->string (get-field sym lit)))
                         (pol (get-field polarity lit))
                         (lit-id (cons var-name pol))
                         (occ (hash-ref lit-weights lit-id))]
                    (hash-set! lit-weights lit-id (- occ 1)))
                  (weights-remove-cl-helper (+ i 1)))]))
  (weights-remove-cl-helper 0))
  

(define (backtrack-search phi assignment) ; backtrack search
    
  (define (find-free-var var-asg) ; find free variable, given assignment var-asg
    (if (null? var-asg) #f
        (if (not (boolean? (cdr (car var-asg)))) (car (car var-asg))
            (find-free-var (cdr var-asg)))))
  
    (cond [(equal? phi #t) (begin (cond [(= opcode 0) (displayln "SAT")]) (display-asg assignment) #t)]
        [(equal? phi #f) #f]
        [(let*[(var-asg-list (hash->list assignment)) ; find branching variable
               (br-var (find-free-var var-asg-list))]
           (begin 
             (let* [(brt-assignment (hash-set assignment br-var #t)) ; set branching variable to #t
                    (t-simp-expr (simplify phi brt-assignment 0))
                    (t_res (backtrack-search t-simp-expr brt-assignment))]
               (if (equal? t_res #t) #t
                   (begin
                     (let* [(brf-assignment (hash-set assignment br-var #f)) ; set branching variable to #f
                            (f-simp-expr (simplify phi brf-assignment 0))
                            (f_res (backtrack-search f-simp-expr brf-assignment))]
                       (if (equal? f_res #t) #t
                           #f)))))))]))  

(define (dpll phi assignment) ; DPLL with a simple branching heuristic
    
  (define (find-free-var var-asg) ; find free variable, given assignment var-asg
    (if (null? var-asg) #f
        (if (not (boolean? (cdr (car var-asg)))) (car (car var-asg))
            (find-free-var (cdr var-asg))))) 

  (define (unit-prop F assignment) ; apply unit propagation, return simplified expression, modify assignment
    (define (traverse F i unit-clauses new-assignment)  ; traverse F, if a clause is a unit clause, modify assignment
      (if (= i (gvector-count F)) (cons (simplify F new-assignment 0) new-assignment)
                                   
          (let*[(cl (gvector-ref F i))
                (len (length cl))]
            (if (= len 1) (let*[(lit (car cl))
                                (pol (get-field polarity lit))
                                (sym (get-field sym lit))]
                            (if (= pol 1) (traverse F (+ i 1) (cons cl unit-clauses) (hash-set assignment (symbol->string sym) #t))
                                (traverse F (+ i 1) (cons cl unit-clauses) (hash-set assignment (symbol->string sym) #f))))
                          
                (traverse F (+ i 1) unit-clauses new-assignment)))))
    (traverse F 0 '() assignment))

  (define (pure-literal-elim F new-assignment) ; apply pure literal elimination
    (define var-table (make-hash)) ; key: variable name, value: pair (polarity, purity)
    (define pure-literals (make-hash)) ; key: variable name, value: polarity
    ;(display " in pure-literal-elim") (newline)
    
    (define (traverse-cl cl j)
      (if (= j (length cl)) pure-literals
          (let*[(lit (list-ref cl j))
                (var-name (symbol->string (get-field sym lit)))
                (lit-pol (get-field polarity lit))]
            (if (not (hash-has-key? var-table var-name)) (begin (hash-set! var-table var-name (cons lit-pol 'pure))
                                                                (hash-set! pure-literals var-name lit-pol)
                                                                (traverse-cl cl (+ j 1)))
                (let*[(hash-val (hash-ref var-table var-name))
                      (pol-table (car hash-val))
                      (purity (cdr hash-val))]
                  (cond [(and (equal? purity 'pure) (not (equal? lit-pol pol-table))) ; variable has occured in both polarities, so impure
                         (begin (hash-set! var-table var-name (cons 0 'impure))
                                (hash-remove! pure-literals var-name))]) ; remove variable from hash table of pure-literals
                  (traverse-cl cl (+ j 1)))))))
    
    (define (get-pure-literals i pure-literals) ; returns a list of (var-name, polarity) pairs
      (if (= i (gvector-count F)) (hash->list pure-literals)
          (let*[(cl (gvector-ref F i))
                (temp-pure-literals (traverse-cl cl 0))]
            (get-pure-literals (+ i 1) temp-pure-literals))))

    (define (assign-pure-literals)
      (let [(pure-literals (get-pure-literals 0 '()))]
        (define (assign-pure-helper i new-assignment)
          (if (= i (length pure-literals)) (cons (simplify F new-assignment 0) new-assignment)
              (let* [(key-val (list-ref pure-literals i))
                     (var-name (car key-val))
                     (pol (cdr key-val))]
                (if (equal? pol 1) (assign-pure-helper (+ i 1) (hash-set new-assignment var-name #t))
                    (assign-pure-helper (+ i 1) (hash-set new-assignment var-name #f))))))
                
        (assign-pure-helper 0 new-assignment)))

    (let [(simp-expr-asg (assign-pure-literals))]
      simp-expr-asg))
     
    (cond [(equal? phi #t) (begin (newline) (cond [(= opcode 0) (displayln "SAT")]) (display-asg assignment) #t)]
        [(equal? phi #f) #f]
                 
        [(let* [(up-phi-asg (unit-prop phi assignment))
                (up-phi (car up-phi-asg))
                (up-assignment (cdr up-phi-asg))]
           (cond [(equal? up-phi #t) (begin (newline) (cond [(= opcode 0) (displayln "SAT")]) (display-asg up-assignment) #t)]
                 [(equal? up-phi #f) #f]
                 [else (let* [(pl-phi-asg (pure-literal-elim up-phi up-assignment))
                              (pl-phi (car pl-phi-asg))
                              (pl-assignment (cdr pl-phi-asg))]
                         (cond [(equal? pl-phi #t) (begin (cond [(= opcode 0) (begin (displayln "SAT"))]) (display-asg pl-assignment) #t)]
                               [(equal? pl-phi #f) #f]
                               ; find branching variable
                               [(let*[(asg-list (hash->list pl-assignment))
                                      (br-var (find-free-var asg-list))]                                                             
                                  (let* [(brt-assignment (hash-set pl-assignment br-var #t)) ; set branching variable to #t
                                         (t-simp-expr (simplify pl-phi brt-assignment 0))
                                         (t_res (dpll t-simp-expr brt-assignment))]
                                    (if (equal? t_res #t) #t
                                        (let* [(brf-assignment (hash-set pl-assignment br-var #f)) ; set branching variable to #f
                                               (f-simp-expr (simplify pl-phi brf-assignment 0))
                                               (f_res (dpll f-simp-expr brf-assignment))]
                                          (if (equal? f_res #t) #t
                                              #f)))))]))]))]))

(define (dpll-dlis phi assignment) ; implement DPLL with DLIS branching heuristic
    
  (define (dlis pl-assignment) ; implement DLIS branching heuristic
    (define (dlis-helper sorted-weights-list)
      (let* [(max-wt-pair (car sorted-weights-list))
             (max-wt-lit (car max-wt-pair))
             (max-wt (cdr max-wt-pair))
             (var-name (car max-wt-lit))
             (var-pol (cdr max-wt-lit))]
        (if (not (boolean? (hash-ref pl-assignment var-name))) (cons var-name var-pol)  ; free variable
            (dlis-helper (cdr sorted-weights-list)))))
    
    (let* [(weights-list (hash->list lit-weights))
           (sorted-weights-list (sort weights-list > #:key (lambda (x) (cdr x))))
           (br-lit (dlis-helper sorted-weights-list))]
      br-lit))
                     
  (define (unit-prop F assignment) ; apply unit propagation, return simplified expression, modify assignment
    (define (traverse F i unit-clauses new-assignment) ; traverse F, if a clause is a unit clause, modify assignment
      (if (= i (gvector-count F)) (cons (simplify F new-assignment 0) new-assignment)
                                   
          (let*[(cl (gvector-ref F i))
                (len (length cl))]
            (if (= len 1) (let*[(lit (car cl))
                                (pol (get-field polarity lit))
                                (sym (get-field sym lit))]
                            (if (= pol 1) (traverse F (+ i 1) (cons cl unit-clauses) (hash-set assignment (symbol->string sym) #t))
                                (traverse F (+ i 1) (cons cl unit-clauses) (hash-set assignment (symbol->string sym) #f))))
                          
                (traverse F (+ i 1) unit-clauses new-assignment)))))
    (traverse F 0 '() assignment))

  (define (pure-literal-elim F new-assignment) ; apply pure literal elimination
    (define var-table (make-hash)) ; key: variable name, value: pair (polarity, purity)
    (define pure-literals (make-hash)) ; key: variable name, value: polarity
        
    (define (traverse-cl cl j)
      (if (= j (length cl)) pure-literals
          (let*[(lit (list-ref cl j))
                (var-name (symbol->string (get-field sym lit)))
                (lit-pol (get-field polarity lit))]
            (if (not (hash-has-key? var-table var-name)) (begin (hash-set! var-table var-name (cons lit-pol 'pure))
                                                                (hash-set! pure-literals var-name lit-pol)
                                                                (traverse-cl cl (+ j 1)))
                (let*[(hash-val (hash-ref var-table var-name))
                      (pol-table (car hash-val))
                      (purity (cdr hash-val))]
                  (cond [(and (equal? purity 'pure) (not (equal? lit-pol pol-table))) ; variable has occured in both polarities, so impure
                         (begin (hash-set! var-table var-name (cons 0 'impure))
                                (hash-remove! pure-literals var-name))]) ; remove variable from hash table of pure-literals
                  (traverse-cl cl (+ j 1)))))))
    
    (define (get-pure-literals i pure-literals) ; returns a list of (var-name, polarity) pairs
      (if (= i (gvector-count F)) (hash->list pure-literals)
          (let*[(cl (gvector-ref F i))
                (temp-pure-literals (traverse-cl cl 0))]
            (get-pure-literals (+ i 1) temp-pure-literals))))

    (define (assign-pure-literals)
      (let [(pure-literals (get-pure-literals 0 '()))]
        (define (assign-pure-helper i new-assignment)
          (if (= i (length pure-literals)) (cons (simplify F new-assignment 0) new-assignment)
              (let* [(key-val (list-ref pure-literals i))
                     (var-name (car key-val))
                     (pol (cdr key-val))]
                (if (equal? pol 1) (assign-pure-helper (+ i 1) (hash-set new-assignment var-name #t))
                    (assign-pure-helper (+ i 1) (hash-set new-assignment var-name #f))))))
                
        (assign-pure-helper 0 new-assignment)))

    (let [(simp-expr-asg (assign-pure-literals))]
      simp-expr-asg))
     
    (cond [(equal? phi #t) (begin (newline) (cond [(= opcode 0) (displayln "SAT")]) (display-asg assignment) #t)]
        [(equal? phi #f) #f]             
        [(let* [(up-phi-asg (unit-prop phi assignment))
                (up-phi (car up-phi-asg))
                (up-assignment (cdr up-phi-asg))]
           (cond [(equal? up-phi #t) (begin (newline) (cond [(= opcode 0) (displayln "SAT")]) (display-asg up-assignment) #t)]
                 [(equal? up-phi #f) #f]
                 [(let* [(pl-phi-asg (pure-literal-elim up-phi up-assignment))
                         (pl-phi (car pl-phi-asg))
                         (pl-assignment (cdr pl-phi-asg))]
                    (cond [(equal? pl-phi #t) (begin (cond [(= opcode 0) (displayln "SAT")]) (display-asg pl-assignment) #t)]
                          [(equal? pl-phi #f) #f]
                          [(let*[(br-var-pol (dlis pl-assignment))
                                 (br-var (car br-var-pol))
                                 (br-pol (cdr br-var-pol))]                                 
                                                                                             
                             (let* [(brt-assignment (cond [(equal? br-pol 1) (hash-set pl-assignment br-var #t)] ; positive branching literal, set to #t
                                                          [(hash-set pl-assignment br-var #f)]))               
                                    (t-simp-expr (simplify pl-phi brt-assignment 1))
                                    (t_res (dpll-dlis t-simp-expr brt-assignment))]
                               (if (equal? t_res #t) #t
                                          
                                   (let* [ (brf-assignment (cond [(equal? br-pol 1) (hash-set pl-assignment br-var #f)] ; set branching variable to #f
                                                                 [(hash-set pl-assignment br-var #t)]))
                                           (f-simp-expr (simplify pl-phi brf-assignment 1))
                                           (f_res (dpll-dlis f-simp-expr brf-assignment))]
                                     (if (equal? f_res #t) #t
                                         #f)))))]))]))]))

(define  (update-table literals) ; updates the initial assignment
  
  (define n (length literals))
  (define (update-helper i)
    (cond [(< i n) (begin (cond [(not (hash-has-key? init-assignment (get-field sym (list-ref literals i))))
                                 (let[(sym_temp (symbol->string (get-field sym (list-ref literals i))))]                                    
                                   (if (char=? #\! (string-ref sym_temp 0)) (let [(sym_i (substring sym_temp 1))]
                                                                              (hash-set! init-assignment sym_i 0))                                                  
                                       (hash-set! init-assignment sym_temp 0)))])                                   
                          (update-helper (+ i 1)))]))
 
  (update-helper 0))

(define (init-weights) ; initialises DLIS weights 
  (define len_formula (gvector-count CNF_formula))
  (define (init-clause cl)
    ; removing duplicate literals to avoid counting multiple occurrences of a literal in the same clause
    (define cl1 (remove-duplicates cl equal? #:key (lambda (lit) (let* [(lit-sym (get-field sym lit))
                                                                        (lit-pol (get-field polarity lit))]
                                                                   (cons lit-sym lit-pol)))))
    (define len (length cl1))
    (define (init-clause-helper i)
      (cond [(< i len)
             (begin (let*[(lit (list-ref cl1 i))
                          (var-name (symbol->string (get-field sym lit)))
                          (pol (get-field polarity lit))
                          (lit-id (cons var-name pol))]
                      (cond [(not (hash-has-key? lit-weights lit-id))
                             (hash-set! lit-weights lit-id 1)]  
                            [else
                             (let[(occ (hash-ref lit-weights lit-id))]
                               (hash-set! lit-weights lit-id (+ occ 1)))]))
                    (init-clause-helper (+ i 1)))]))

    (init-clause-helper 0))
  
  (define (init-weights-helper i)
    (cond [(< i len_formula)
           (let*[(cl (gvector-ref CNF_formula i))]
             (init-clause cl)
             (init-weights-helper (+ i 1)))]))

  (init-weights-helper 0))
      
                          
(define (init)  ; initialisation
  (define n (gvector-count CNF_formula))
  (define (init-helper i)
    (cond [(< i n)
           (let* [(l (gvector-ref CNF_formula i))]
             (begin (update-table l)
                    (init-helper (+ i 1))))]))
  (init-helper 0))


  (define (formula-maker l i out) ; converts Sudoku input to a formula as a list of lists
  (define (per-div i j)
  (if (= 0 (remainder i j))
      (/ i j)
      (+ 1 (floor (/ i j)))))
(define (per-mod i j)
  (if (= 0 (remainder i j))
      j
      (remainder i j)))
  
  (if (= i 17)
      out
      (let*[(row (per-div i 4))
            (col (per-mod i 4))]
        (if(equal? (car l) #\.)
           (formula-maker (cdr l) (+ i 1) out)
           (formula-maker (cdr l) (+ i 1)
                          (cons (list (string->symbol(string-append "x"
                                                            (number->string (+ (- (char->integer (car l)) 48) (* 10 col) (* 100 row)))))) out))))))

(define (inrange x) ; returns true if all characters in x are either 1, 2, 3, 4 or .
  (andmap inrange-helper (string->list x)))

(define (inrange-helper c) ; checks if c is 1, 2, 3, 4 or .
  (or (char=? c #\1)(char=? c #\2)(char=? c #\3)(char=? c #\4)(char=? c #\.)))
  

(define (get-input)
  (display "Enter First row")(newline)
  (define x1 (read))
  (display "Enter Second row")(newline)
  (define x2 (read))
  (display "Enter Third row")(newline)
  (define x3 (read))
  (display "Enter Last row")(newline)
  (define x4 (read))
  (if (not (and (string? x1) (string? x2) (string? x3) (string? x4))) (display "Invalid input. Input must be a string")
  (let [(x (string-append x1 x2 x3 x4))]
    (if (and (inrange x) (= (string-length x) 16))
      (let*[(l (string->list x))
           (F (formula-maker l 1 '()))]
        (solve-sudoku F))    
      (begin(displayln "Incorrect Input") (get-input))))))

;; functions for taking formula as input

(define (is-negative? sym)
  (define str (symbol->string sym))
  (if (regexp-match #rx"-." str)
      #t
      #f))

(define (get_user_input list_of_lists)
  (cond [(not (null? list_of_lists))
         (let([cl (make-clause (car list_of_lists) '())])
           (gvector-add! CNF_formula cl)
           (get_user_input (cdr list_of_lists)))]))

(define (shed-negative sym)
  (let*([str (symbol->string sym)]
        [new_str (substring str 1)])
    (string->symbol new_str)))


(define (make-clause l out)
  (if (null? l)
      out
      (if (is-negative? (car l))
          (make-clause (cdr l) (cons (make-object literal% (shed-negative (car l)) -1) out))
          (make-clause (cdr l) (cons (make-object literal% (car l) 1) out)))))



; input format : list 
(define (solve-sudoku input)
  (define F (append input sudoku-four))
  (solve F))


;; display functions to print the board

(define (print-board sorted-asg n)
  (define (print-board-helper i)
    (cond [(<= i (* n n))
           (let* [(pos (list-ref sorted-asg (- i 1)))
                  (val (cdr pos))]
             (if (equal? val #t) (display "Q")
                 (display "-"))
             (if (= (remainder i n) 0) (newline)
                 (display " "))
             (print-board-helper (+ i 1)))]))
  (begin (newline)(print-board-helper 1)))

(define (print-board-sudoku sorted-asg)
  (define (print-board-helper i)
    (cond [(<= i 16)
           (let* [(pos (list-ref sorted-asg (- i 1)))
                  (val (cdr pos))
                  (lit-name (car pos))]
             (display (substring lit-name (- (string-length lit-name) 1))) ; distinguish between original blank squares?
             (if (= (remainder i 4) 0) (newline)
                 (display " "))
             (print-board-helper (+ i 1)))]))
  (begin (newline) (print-board-helper 1)))
;(display sorted-asg))
             
                 
(define (display-queens assignment n)  ; display function for eight queens (n = 8) and four queens (n = 4) problems. n is the dimension of the board
  (let* [(asg-list (hash->list assignment))
         (sorted-asg (sort asg-list string<? #:key (lambda (x) (car x))))]
    (print-board sorted-asg n)))

(define (display-sudoku assignment) ; display function for Sudoku problem
  (let* [(asg-list (hash->list assignment))
         (filtered-list (filter (lambda (x) (equal? (cdr x) #t)) asg-list))
         (sorted-asg (sort filtered-list string<? #:key (lambda (x) (car x))))
         ]
    (print-board-sudoku sorted-asg)))

(define (display-sat assignment) ; display function for satisfiability problem
  (define asg-list (hash->list assignment))
  (define len (length asg-list))
  (define (display-sat-helper i)
    (cond [(< i len) (let* [(var-val (list-ref asg-list i))
                                  (var (car var-val))
                                  (val (cdr var-val))]
                             (display var) (display ":")
                       (cond [(equal? val #t) (display "True")]
                                                               [(equal? val #f) (display "False")]
                                                               [else (display "Unassigned")])
                       (display " ")
                       (display-sat-helper (+ i 1)))]))
  
  (display-sat-helper 0))


(define (display-asg assignment) ; chooses display function according to opcode
  (cond [(= opcode 0) (display-sat assignment)]; SAT
        [(= opcode 1) (display-queens assignment 4)]
        [(= opcode 2) (display-sudoku assignment)]
        [(= opcode 3) (display-queens assignment 8)]))

(define (clear-formula CNF_formula)  ; removes all elements in CNF_formula
  (cond [(> (gvector-count CNF_formula) 0) (begin
                                             (gvector-remove-last! CNF_formula)
                                             (clear-formula CNF_formula))]))

(define (continue) ; provides option to continue
  (displayln "Enter 1 to continue, 0 to exit.")
  (let [(option (read))]
    (cond [(equal? option 1) (main)]
          [(not (equal? option 0)) (begin (displayln "Invalid option") (continue))])))

(define (solve_dpll exp) ; checks satisfiability of exp using dpll
  (get_user_input exp)
  (init)
  (define var-assignment (make-immutable-hash (hash->list init-assignment)))
  (define res (dpll CNF_formula var-assignment))
  (cond [(void? res)
          (if (= opcode 0) (display "UNSAT")
              (display "No solution"))])
  (hash-clear! init-assignment)
  (hash-clear! lit-weights))
  
  
(define (solve_dpll-dlis exp) ; checks satisfiability of exp using dpll-dlis
  (get_user_input exp)
  (init)
  (init-weights)
  (define var-assignment (make-immutable-hash (hash->list init-assignment)))
  (define res (dpll-dlis CNF_formula var-assignment))
  (cond [(void? res)
          (if (= opcode 0) (display "UNSAT")
              (display "No solution"))])
  (hash-clear! init-assignment)
  (hash-clear! lit-weights))
    

(define (solve_backtrack exp) ; checks satisfiability of exp using backtrack search
  (get_user_input exp)
  (init)
  (define var-assignment (make-immutable-hash (hash->list init-assignment)))
  (define res (backtrack-search CNF_formula var-assignment))
   (cond [(void? res)
          (if (= opcode 0) (display "UNSAT")
              (display "No solution"))])
  (hash-clear! init-assignment)
  (hash-clear! lit-weights))
  
  
(define (solve F) ; chooses function according to method-code
  (cond [(= method-code 0) (let[(res (solve_backtrack F))] res)]
        [(= method-code 1) (let [(res (solve_dpll F))] res)]
        [(= method-code 2) (solve_dpll-dlis F)])
  (newline)
  (continue))
           
(define (main)
  (clear-formula CNF_formula)
  (displayln "0 : Satisfiability")
  (displayln "1 : Four queens")      
  (displayln "2 : Sudoku")
  (displayln "3 : Eight queens")
  (displayln "Enter code:")
  (define x (read))
  (set! opcode x)
  (display "0 : Backtrack search") (newline)
  (display "1 : DPLL") (newline)
  (display "2 : DPLL with DLIS heuristic") (newline)
  (display "Enter code:") (newline)
  (define m (read))
  (cond [(not (or (= m 0) (= m 1) (= m 2))) (begin (displayln "Invalid code.") (main))])
  (set! method-code m)
  (cond [(= opcode 0) (display "(solve F) checks satisfiability of F. F must be a list of lists.")]
        [(= opcode 1) (solve four-queens)]
        [(= opcode 2) (begin (display "Enter Constraints as Strings (along with double quotation marks). Note that . stands for no constraint")(newline)(get-input))]
        [(= opcode 3) (solve eight-queens)]
        [else (begin (displayln "Invalid code.") (main))]))

  
                     
                     



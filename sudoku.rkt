#lang racket
(provide
 enter-and-solve)

;; board is a vector unless otherwise specified

(define UNDO_VALUE "undo")
(define NON_REPLACABLE_STRING_CODES (list "n" "~" " "))
(define INVALID_BOARD_INDEX 81) ;; the 81st index of the board is to say wether or not the board is valid
(define SETTING_CELL_VALUE '*)
(define INVALID_BOARD_VALUE (list "INVALID BOARD"))
(define (invalidate-board board) (vector-set! board INVALID_BOARD_INDEX INVALID_BOARD_VALUE))

(define (contains? l element) (integer? (index-of l element)))

(define (board-index-of row column) (+ (* row 9) column))
(define (row-of    index) (quotient index 9))
(define (column-of index) (modulo   index 9))

(define (get-value board row column)
  (vector-ref board (board-index-of row column)))
(define (set-value board row column new-value)
  (define previously-unknown? (not (known-cell? board row column)))
  (vector-set! board (board-index-of row column) new-value)
  (cond
    [(empty? new-value) (invalidate-board board)]
    [(and (valid? board) previously-unknown? (known-value? new-value))
     ;; We update notes if this value goes from being unkown to known
     (update-notes board row column)]))

(define (get-value-position board position)           (get-value board (car position) (cdr position)))
(define (set-value-position board position new-value) (set-value board (car position) (cdr position) new-value))

;; The following functions return lists of positions (row . column) of that group
(define (get-row-positions board row)       (map (λ (column) (cons row column)) (range 0 9)))
(define (get-column-positions board column) (map (λ (row)    (cons row column)) (range 0 9)))

;; Square groups:
;;0|1|2
;;-----
;;3|4|5
;;-----
;;6|7|8
(define (get-square-positions board square-number)
  (define top-left-row    (* (quotient square-number 3) 3))
  (define top-left-column (* (modulo   square-number 3) 3))
  (map
   (λ (value-on)
     ;; Moves through ther square like so:
     ;; 0 1 2
     ;; 3 4 5
     ;; 6 7 8
     (define row    (+ top-left-row    (quotient value-on 3)))
     (define column (+ top-left-column (modulo   value-on 3)))
     (cons row column))
   (range 0 9)))

;; Makes a list of all the positions in a group with a given cell
(define (get-all-cell-group-positions board row column)
  (append
   (get-row-positions board row)
   (get-column-positions board column)
   (get-square-positions board (get-square-number row column))))
  
(define (positions->values board positions)
  (map (λ (position) (get-value-position board position)) positions))

(define (get-row-group    board row)           (positions->values board (get-row-positions            board row)))
(define (get-column-group board column)        (positions->values board (get-column-positions         board column)))
(define (get-square-group board square-number) (positions->values board (get-square-positions         board square-number)))
(define (get-cell-groups  board row column)    (positions->values board (get-all-cell-group-positions board row column)))

;; Puts all the groups of a board in a 2d list
(define (get-all-groups board)
  (append
   (map (λ (row)           (get-row-group    board row))           (range 0 9))
   (map (λ (column)        (get-column-group board column))        (range 0 9))
   (map (λ (square-number) (get-square-group board square-number)) (range 0 9))))

;; Invalidates the board if it has a duplicate
(define (check-board-for-duplicates board)
  (cond
    [(ormap group-has-duplicates? (get-all-groups board))
     (invalidate-board board)]))

;; Gives the number of a given position's square group
(define (get-square-number row column)
  (+ (* (quotient row 3) 3) (quotient column 3)))

(define (group-has-duplicates? group)
  (define known-cells (filter known-value? group))
  (not (equal? (length known-cells) (length (remove-duplicates known-cells)))))

;; This is a slow way of taking notes. It is done only at the start
(define (note-take-cell board row column)
  (match (get-value board row column)
    [(? unknown-value? value)
     (filter
      (λ (possibility) (not (contains? (get-cell-groups board row column) (list possibility))))
      (range 1 10))]
    [value value]))
(define (note-take-index board index)
  (vector-set! board index (note-take-cell board (row-of index) (column-of index))))
(define (full-note-take board)
  (define old-board (vector-copy board))
  (for-each (λ (i) (note-take-index board i)) (range 0 (* 9 9)))
  (cond
    ;; Continously calls itself until there are no more inferences to be made
    [(not (equal? board old-board)) (full-note-take board)]
    [else (check-board-for-duplicates board)]))

(define (update-cell-notes board position get-rid-of)
  (set-value-position
   board position
   (filter (λ (possibility) (not (equal? possibility get-rid-of))) (get-value-position board position))))
;; This will make sure that none of the other cells in a group with the given cell
;; have the value of this cell
;; If the cell does not have a known value, then it does nothing
(define (update-notes board updated-row update-column)
  (cond
    [(known-cell? board updated-row update-column)
     (define get-rid-of (first (get-value board updated-row update-column)))
     (for-each
      (λ (position)
        (cond
          [(not (equal? position (cons updated-row update-column)))
           (update-cell-notes board position get-rid-of)]))
      (get-all-cell-group-positions board updated-row update-column))]))

(define (complete? board)
  (define (list-complete? board-list)
    (or
     (empty? (rest board-list)) ;; We check if it only has 1 thing, b/c the last cell says wether it is a valid board
     (and (known-value? (first board-list)) (list-complete? (rest board-list)))))
  (list-complete? (vector->list board)))

(define (invalid? board)
  (equal? (vector-ref board INVALID_BOARD_INDEX) INVALID_BOARD_VALUE))
(define (valid? board) (not (invalid? board)))

;; This will generate one board for each possibility of a given cell
(define (guess board row column)
  (map
   (λ (possiblity)
     (define new-board (vector-copy board))
     (set-value new-board row column (list possiblity))
     new-board)
   (get-value board row column)))

;; Checks if a value means that the cell is known: (list 0) -> false, (list 1) -> true, (list 3 4) -> false
(define (known-value? value)
  (and (not (empty? value)) (empty? (rest value)) (not (equal? value (list 0)))))
(define (unknown-value? value) (not (known-value? value)))
(define (known-cell? board row column)
  (known-value? (get-value board row column)))

;; It finds the next cell that has a certian length
(define (next-cell-of-length board row column l)
  (cond
    [(> column 8) (next-cell-of-length board (+ row 1) 0 l)]
    [(> row 8) (cons -1 -1)]
    [(not (= (length (get-value board row column)) l)) (next-cell-of-length board row (+ column 1) l)]
    [else (cons row column)]))
(define (best-guess-from board l-on)
  (match (next-cell-of-length board 0 0 l-on)
    [(cons -1 -1) (best-guess-from board (+ l-on 1))]
    [position position]))
;; Looks for an unkown cell with the least amount of possibilities
(define (best-guess board) (best-guess-from board 2))

;; Simply walks through a list of guesses, tries solving them until it finds a solvable one
(define (first-solvable guesses)
  (if (empty? (cdr guesses))
      (solve-board (car guesses))
      (match (solve-board (car guesses))
        [(? valid? board) board]
        [else (first-solvable (cdr guesses))])))

(define (solve-board board)
  (cond
    [(or (complete? board) (invalid? board)) board]
    [else
     ;; No more basic inferences, so we guess
     (define guess-position (best-guess board))
     (define guesses (guess board (car guess-position) (cdr guess-position)))
     (first-solvable guesses)]))

(define (solve-and-display board)
  (display-board (solve-board board)))

(define (empty-board)
  (make-vector (+ (* 9 9) 1) (list 0)))

(define (cell->displayable cell)
  (if (known-value? cell)
      (first cell)
      '_))

(define (print-formatted-list string l)
  (define (helper strings l)
    (match strings
      [(list) ""]
      [(list string) string]
      [(list string1 string2 others ...)
       (define new-string1 (string-append string1 "~" (substring string2 0 1)))
       (define new-string2 (substring string2 1))
       (if (contains? NON_REPLACABLE_STRING_CODES (substring string2 0 1))
           (set! new-string1 (format new-string1))
           (set! new-string1 (format new-string1 (first l))))
       (string-append new-string1 (helper (cons new-string2 others) (rest l)))]))
  (printf (helper (string-split string "~") l)))

(define (display-board board)
  (if (invalid? board)
      (printf "THE BOARD IS INVALID :(")
      (print-formatted-list
       "
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
---------------------
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
---------------------
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
~s ~s ~s | ~s ~s ~s | ~s ~s ~s 
~s ~s ~s | ~s ~s ~s | ~s ~s ~s
"
       (map cell->displayable (vector->list board)))))

(define (read-line-until f)
  (define answer (read-line))
  (if (f answer)
      answer
      (read-line-until f)))

;; allows one to enter the board
(define (enter-board-from board cell-on)
  (cond
    [(= cell-on (* 9 9))
     (display-board board)
     (printf "solving board...~n")
     board]
    [else
     ;; makes the board to display different so that it can change the look of the value
     ;; you are currently editting
     (define board-to-display (vector-copy board))
     (vector-set! board-to-display cell-on (list SETTING_CELL_VALUE))
     (display-board board-to-display)
     (printf "~nif a cell is empty, simply input 0~n")
     (printf "if you messed up, simply input \"undo\"~n")
     (define next-cell
       (read-line-until
        (λ (x)
          (define n (string->number x))
          (or (equal? x UNDO_VALUE)
              (and (integer? n) (< n 10) (> n -1))))))
     (if (equal? next-cell UNDO_VALUE)
         (enter-board-from board (- cell-on 1))
         (begin
           (vector-set! board cell-on (list (string->number next-cell)))
           (enter-board-from board (+ cell-on 1))))]))

(define (enter-board)
  (define board (enter-board-from (empty-board) 0))
  (full-note-take board)
  board)

(define (enter-and-solve)
  (solve-and-display (enter-board)))

(enter-and-solve)
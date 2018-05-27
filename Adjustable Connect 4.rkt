#lang racket

(define ROWS 24)
(define COLUMNS 25)
(define LENGTH 7)


(define (nth n l)
  (if (= n 1)
      (car l)
      (nth (- n 1) (cdr l))))

(define (newBoard)
  (define (newBoardh on)
    (if (= on 0)
        (list)
        (cons 0 (newBoardh (- on 1)))))
  (newBoardh (* ROWS COLUMNS)))

(define (position r c)
  (+ (* (- r 1) COLUMNS) c))

(define (setPosition l n e)
  (if (= n 1)
      (cons e (cdr l))
      (cons (car l) (setPosition (cdr l) (- n 1) e))))

(define (spot b r c)
  (nth (position r c) b))

(define (full? b)
  (define (fullh b on)
    (cond
      ((> on COLUMNS) #t)
      ((= (car b) 0) #f)
      (else (fullh (cdr b) (+ on 1)))))
  (fullh b 1))

(define (winnerSingle l)
  (cond
    ((empty? (cdr l)) (car l))
    ((= (car l) (winnerSingle (cdr l))) (car l))
    (else 0)))

(define (rowSingle b r c rd cd)
  (define (rowSingleh b r c on rd cd)
    (if (> on LENGTH)
        (list)
        (cons (spot b r c)
              (rowSingleh b (+ r rd) (+ c cd) (+ on 1) rd cd))))
  (rowSingleh b r c 1 rd cd))

(define (allPossibleRows b)
  (define (allPossibleRowsh b r c)
    (cond
      ((> r ROWS)(list))
      ((> c COLUMNS) (allPossibleRowsh b (+ r 1) 1))
      (else (begin
              (define theRest (allPossibleRowsh b r (+ c 1)))
              (cond
                ((> (- ROWS r) (- LENGTH 2)) (set! theRest (cons
                                                            (rowSingle b r c 1 0)
                                                            theRest))))
              (cond
                ((> (- COLUMNS c) (- LENGTH 2)) (set! theRest (cons
                                                               (rowSingle b r c 0 1)
                                                               theRest))))
              (cond
                ((and (> (- ROWS r) (- LENGTH 2))
                      (> (- COLUMNS c) (- LENGTH 2)))
                 (set! theRest (cons
                                (rowSingle b r c 1 1)
                                theRest))))
              (cond
                ((and (> (- r ROWS) (- LENGTH 2))
                      (> c 3))
                 (set! theRest (cons
                                (rowSingle b r c 1 0)
                                theRest))))
              theRest))))
  (allPossibleRowsh b 1 1))
  
(define (mostL l f)
  (if (empty? (cdr l))
      (car l)
      (f (car l) (mostL (cdr l) f))))

(define (minL l)
  (mostL l min))

(define (maxL l)
  (mostL l max))

(define (over b)
  (define w
    (map winnerSingle (allPossibleRows b)))
  (cond
    ((= (maxL w) 1) 1)
    ((= (minL w) -1) -1)
    ((full? b) 0)
    (else 10)))

(define (play b c v)
  (define (playh r)
    (cond
      ((= r 0) -1)
      ((= (spot b r c) 0) (setPosition b (position r c) v))
      (else (playh (- r 1)))))
  (if (or (< c 1) (> c COLUMNS))
      false
      (playh ROWS)))

(define (sumL l)
  (cond ((empty? l) 0) (else (+ (car l) (sumL (cdr l))))))

(define (string->integer str)
  (define (string->integerh chars)
    (cond
      ((empty? chars) 0)
      (else (+ (char->integer (car chars)) -48
               (* 10 (string->integerh (cdr chars)))))))
  (string->integerh (reverse (string->list str))))


(define (makeSeperator)
  (define (makeSeperator-h on)
    (if (= on 0)
        ""
        (string-append "-" (makeSeperator-h (- on 1)))))
  (string->symbol (makeSeperator-h (+ (* COLUMNS 2) 1))))
        
(define (printBoard b)
  
  (define (toSymbol v)
    (cond
      ((= v 1) 'X)
      ((= v -1) 'O)
      (else '_ )))
  
  (define (printBoard-h b r c)
    (cond
      ((> r ROWS) (printf "~n"))
      ((> c COLUMNS) (printBoard-h b (+ r 1) 1))
      (else
       (begin
         (define s (toSymbol (car b)))
         (cond
           ((= c 1) (printf "~n|")))
         (if (= (car b) 0)
                     (printf " |")
                     (printf "~s|" s))
         (printBoard-h (cdr b) r (+ c 1))))))
  (printBoard-h b 1 1)
  (printf "~s~n" (makeSeperator)))

(define (twoPlayers)
  (define (twoPlayersh b turn)
    (define o (over b))
    (cond
      ((= o 1)(printf "p1"))
      ((= o -1)(printf "p2"))
      ((= o 0) (printf "draw"))
      (else
       (begin
         (printBoard b)
         (printf "column: ~n")
         (define c (string->integer (read-line)))
         (define newB (play b c turn))
         (if (boolean? newB)
             (twoPlayersh b turn)
             (twoPlayersh newB (- 0 turn)))))))
  (twoPlayersh (newBoard) 1))
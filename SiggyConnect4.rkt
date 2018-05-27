#lang racket

(define (nth l n)
  (if (= n 1)
       (car l)
      (nth (cdr l) (- n 1))))

(define (newBoard)
  (list (list 0 0 0 0 0 0)
        (list 0 0 0 0 0 0)
        (list 0 0 0 0 0 0)
        (list 0 0 0 0 0 0)
        (list 0 0 0 0 0 0)
        (list 0 0 0 0 0 0)
        (list 0 0 0 0 0 0)))

(define (position b c r)
  (nth (nth b c) r))

(define (set-position-h c r v)
  (if (= r 1)
      (cons v (cdr c))
      (cons (car c)
            (set-position-h (cdr c) (- r 1) v))))
  
(define (set-position b c r v)
  (if (= c 1)
      (cons (set-position-h (car b) r v)(cdr b))
      (cons (car b)
            (set-position (cdr b) (- c 1) r v))))

(define (contains? l v)
  (and (not (empty? l))
       (or (= (car l) v)
           (contains? (cdr l) v))))

(define (full? b)
  (or (empty? b)
      (and (not (contains? (car b) 0))
          (full? (cdr b)))))
      
(define (place b c v)
  (define (place-h r)
    (if (= (position b c r) 0)
        r
        (place-h (- r 1))))
  (if (= (position b c 1) 0)
      (set-position b c (place-h 6) v)
      -1))

(define (xo n)
  (if (= n 1)
      "x"
      (if (= n -1)
          "o"
          " ")))

(define (printRow b r con)
  (if (= con 7)
      ;"~s~n"
      (printf (string-append (xo (position b con r)) "|~n"))
      (begin
        (printf (string-append (xo (position b con r)) "|"))
        (printRow b r (+ con 1)))))

(define (printBoard b)
  (define (printBoard-h ron)
    (printf "|")
    (if (= ron 6)
        (printRow b ron 1)
        (begin
          (printRow b ron 1)
          (printf "---------------~n")
          (printBoard-h (+ ron 1))
          )))
  (printBoard-h 1)
  (printf "---------------~n"))

(define (allSame? l)
  (or (empty? (cdr l))
      (and (= (car l)(cadr l))
          (allSame? (cdr l)))))

;; returns the four in a row the first element being (ron,con) and each conequetive element is ron more r and con more c
(define (getFour b ron con rdir cdir)
  (define (getFour-h b ron con on rdir cdir)
    (if (= on 5)
        (list)
        (cons (position b con ron)
              (getFour-h b (+ ron rdir) (+ con cdir) (+ on 1) rdir cdir))))
  (getFour-h b ron con 1 rdir cdir))

(define (getFours b rdir cdir)
  (define (getFours-h ron con)
    (cond
      ((or (= con 8) (= (+ (* 3 cdir) con) 8))
        (begin
          (set! con 1)
          (set! ron (+ ron 1)))))
    (cond
      ((and (= rdir -1) (= ron 1))
       (set! ron 4))
      ((and (= cdir -1) (= con 1))
       (set! con 4)))
    (if (or (= ron 7) (= (+ (* 3 rdir) ron) 7))
        (list)
        (cons
         (getFour b ron con rdir cdir)
         (getFours-h ron (+ con 1)))))
  (getFours-h 1 1))

(define (getAllFours b)
  (append (getFours b 1 1)(getFours b 1 0)(getFours b 0 1)(getFours b -1 1)))

(define (winner b)
  (define (winner-h l)
    (cond
      ((empty? l) 0)
      ((and (allSame? (car l)) (not (= (caar l) 0))) (caar l))
      (else (winner-h (cdr l)))))
  (winner-h (getAllFours b)))

(define (over? b)
  (or (not (= (winner b) 0)) (full? b)))

(define (play)
  (define (play-h b p)
    (printBoard b)
    (define ans "bugleshnu")
    (if (over? b)
        (printf (string-append "And the winner is... " (xo(winner b)) "!"))
        (begin
          (printf (string-append "Where would you like to go " (xo p) "?~n"))
          (set! ans (string->number (read-line)))
          (play-h (place b ans p) (* p -1)))))
  (play-h (newBoard) 1))

(play)
          
          
          
          
      
  


#lang racket

(define (myPoem on)
  (if (= on -1)
      (printf "TERMINATION")
      (begin
        (if (= (modulo on 4) 3)
            (printf "I ")
            (if (= (modulo on 4) 2)
                (printf "am ")
                (if (= (modulo on 4) 1)
                    (printf "a ")
                    (printf "poem!~n"))))
        (myPoem (- on 1))
        )))
(myPoem 99)

  
  
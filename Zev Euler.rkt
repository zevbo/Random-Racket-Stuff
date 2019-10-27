#lang racket
(require math/base)
(require math/number-theory)
(require test-engine/racket-tests)

(define (rlist->num l)
  (if (empty? l)
      0
      (+ (car l) (* 10 (rlist->num (cdr l))))))

(define (list->num l)
  (rlist->num (reverse l)))

(define (factor fact num)
  (integer? (/ num fact)))

(define (p#1h numon lis)
  (if (= numon 0)
      (sum lis)
      (if (or (factor 5 numon) (factor 3 numon))
          (p#1h (- numon 1) (cons numon lis))
          (p#1h (- numon 1) lis))))

(define (p#1)
  (p#1h 999 (list)))

(define (last_list lis)
  (if (empty? (cdr lis))
      (car lis)
      (last_list (cdr lis))))

(define (revh lis newlis)
  (if (empty? lis)
      newlis
      (revh (cdr lis) (cons (car lis) newlis))))

(define (rev lis)
  (revh lis (list)))

(define (droph lis newlis)
  (if (empty? (cdr lis))
      (rev newlis)
      (droph (cdr lis) (cons (car lis) newlis))))

(define (drop lis)
  (droph lis (list)))

(define (lengthh lis num)
  (if (empty? lis)
      num
      (lengthh (cdr lis) (+ num 1))))

(define (length_lis lis)
  (lengthh lis 0))

(define (evensh lis newlis)
  (if (empty? lis)
      (rev newlis)
      (if (integer? (/ (car lis) 2))
          (evensh (cdr lis) (cons (car lis) newlis))
          (evensh (cdr lis) newlis))))

(define (evens lis)
  (evensh lis (list)))

(define (p#2h lis)
  (if (> (last_list lis) 4000000)
      (sum (evens (drop lis)))
      (p#2h (rev (cons (+ (last_list lis) (last_list (drop lis))) (rev lis))))))

(define (p#2)
  (p#2h (list 1 2)))

(define (largeh lis big)
  (if (empty? lis)
      big
      (if (> (car lis) big)
          (largeh (cdr lis) (car lis))
          (largeh (cdr lis) big))))

(define (large_list lis)
  (largeh (cdr lis) (car lis)))

(define (p#3h num lis at)
  (if (> (* at at) num)
      num
      (if (factor at num)
          (flatten (cons (p#3h at (list 1) 2) (p#3h (/ num at) (list 1) 2)))
          (p#3h num lis (+ at 1)))))


(define (pf num)
  (p#3h num (list 1) 2))

(define (l-nh lis num on)
  (if (empty? lis)
      num
      (l-nh (drop lis) (+ num (* (last_list lis) (expt 10 on))) (+ on 1))))


(define (list-num lis)
  (l-nh lis 0 0))

(define (n-lh num lis)
  (if (= num 0)
      lis
      (n-lh (quotient num 10) (cons (remainder num 10) lis))))

(define (num-list num)
  (n-lh num (list)))

(define (pall? lis)
  (equal? lis (rev lis)))

(define (pal? num)
  (pall? (num-list num)))

(define (p#4h lis num1 num2)
  (if (and (= num1 100) (= num2 100))
      (length_lis lis)
      (if (pal? (* num1 num2))
          (if (= num1 100)
              (p#4h (cons (* num1 num2) lis) 999 (- num2 1))
              (p#4h (cons (* num1 num2) lis) (- num1 1) num2))
          (if (= num1 100)
              (p#4h lis 999 (- num2 1))
              (p#4h lis (- num1 1) num2)))))


(define (p#4)
  (p#4h (list) 999 999))

(define (factors? num check)
  (if (= num 1)
      true
      (if (= 0 (remainder check num))
          (factors? (- num 1) check)
          false)))

(define (p#5h num on)
  (if (factors? num on)
      on
      (p#5h num (+ on num))))

(define (p#5 num)
  (p#5h num num))

(define (adduph num su)
  (if (= num 1)
      (+ su 1)
      (adduph (- num 1) (+ su num))))

(define (addup num)
  (adduph num 0))

(define (poweruph num su)
  (if (= num 1)
      (+ su 1)
      (poweruph (- num 1) (+ su (expt num 2)))))

(define (powerup num)
  (poweruph num 0))

(define (p#6 num)
  (- (expt (addup num) 2) (powerup num)))

(define (p#7h end lis on)
  (if (= (length_lis lis) end)
      (car lis)
      (if (prime? on)
          (p#7h end (cons on lis) (+ on 1))
          (p#7h end lis (+ on 1)))))

(define (p#7 num)
  (p#7h num (list) 1))

(define (fronth lis new num on)
  (if (< num on)
      (rev new)
      (fronth (cdr lis) (cons (car lis) new) num (+ on 1))))

(define (front num lis)
  (fronth lis (list) num 1))

(define (prodlh lis num)
  (if (empty? lis)
      num
      (prodlh (cdr lis) (* num (car lis)))))

(define (prodl lis)
  (prodlh lis 1))

(define (p#8h lis biggest)
  (if (= 12 (length_lis lis))
      biggest
      (if (> (prodl (front 13 lis)) biggest)
          (p#8h (cdr lis) (prodl (front 13 lis)))
          (p#8h (cdr lis) biggest))))

(define (p#8 num)
  (p#8h (num-list num) 0))

(define (poth? a b c)
  (and (= (+ (expt a 2) (expt b 2)) (expt c 2)) (> c b a)))

(define (haspo a b)
  (if (and (integer? (sqrt (+ (expt a 2) (expt b 2)))) (> b a))
      (sqrt (+ (expt a 2) (expt b 2)))
      0))

(define (haspo? a b)
  (and (integer? (sqrt (+ (expt a 2) (expt b 2)))) (> b a)))

(define (p#9h num1 num2)
  (if (and (haspo? num1 num2) (= 1000 (+ num1 num2 (haspo num1 num2))))
      (* num1 num2 (haspo num1 num2))
      (if (= num1 1)
          (p#9h 999 (- num2 1))
          (p#9h (- num1 1) num2))))

(define (p#9)
  (p#9h 999 999))

(define (p#10h lis on max)
  (if (> on max)
      (sum lis)
      (if (prime? on)
          (p#10h (cons on lis) (+ on 2) max)
          (p#10h lis (+ on 2) max))))

(define (p#10 max)
  (p#10h (list 2) 3 max))

(define (frontd lis amount)
  (if (= amount 0)
      lis
      (frontd (cdr lis) (- amount 1))))

(define (mult4 lis p1 p2 p3 p4)
  (* (car (frontd lis p1)) (car (frontd lis p2)) (car (frontd lis p3)) (car (frontd lis p4))))

(define (p#11h lis big)
  (if (= (length_lis lis) 3)
      big
      (if (< (length_lis lis) 58)
          (p#11h (cdr lis) (large_list (cons (mult4 lis 0 1 2 3)(cons big (list)))))
          (if (< (length_lis lis) 61)
              (p#11h (cdr lis) (large_list (cons (mult4 lis 0 19 38 57) (cons (mult4 lis 0 1 2 3)(cons big (list))))))
              (if (< (length_lis lis) 64)
                  (p#11h (cdr lis) (large_list (cons (mult4 lis 0 20 40 60) (cons (mult4 lis 0 19 38 57) (cons (mult4 lis 0 1 2 3)(cons big (list)))))))
                  (p#11h (cdr lis) (large_list (cons (mult4 lis 0 21 42 53) (cons (mult4 lis 0 20 40 60) (cons (mult4 lis 0 19 38 57) (cons (mult4 lis 0 1 2 3)(cons big (list)))))))))))))


(define (p#11 lis)
  (p#11h lis 0))

(define (factor#h num on amount)
  (if (= on 1)
      amount
      (if (factor on num)
          (factor#h num (- on 1) (+ amount 1))
          (factor#h num (- on 1) amount))))

(define (factor# num)
  (factor#h num (- num 1) 2))

(define (splitnh num split new)
  (if (empty? num)
      new
      (splitnh (frontd num split) split (cons (list-num (front split num)) new))))


(define (splitn num split)
  (splitnh (num-list num) split (list)))

(define (p#13 num)
  (list-num (front 10 (num-list (sum (splitn num 50)))))) 

(define (collatz_lenh num amount)
  (if (= num 1)
      amount
      (if (even? num)
          (collatz_lenh (/ num 2) (+ amount 1))
          (collatz_lenh (+ (* num 3) 1) (+ amount 1)))))

(define (collatz_len num)
  (collatz_lenh num 1))

(define (p#14h high big biggest on)
  (if (= on high)
      big
      (if (> (collatz_len on) biggest)
          (p#14h high on (collatz_len on)(+ on 1))
          (p#14h high big biggest (+ on 1)))))

(define (p#14 high)
  (p#14h high 0 0 10))

(define (choose num1 num2)
  (/ (factorial num1) (* (factorial num2) (factorial (- num1 num2)))))

(define (letter_2h2 num1 num2)
  (if (= num1 2)
      (+ num2 3)
      (if (= num1 3)
          (+ num2 5)
          (if (= num1 4)
              (+ num2 4)
              (if (= num1 5)
                  (+ num2 4)
                  (if (= num1 6)
                      (+ num2 3)
                      (if (= num1 7)
                          (+ num2 5)
                          (if (= num1 8)
                              (+ num2 5)
                              (if (= num1 9)
                                  (+ num2 4)
                                  (if (= num1 1)
                                      (+ num2 3)
                                      num2))))))))))


(define (letter_2h1 lis)
  (if (= (car lis) 2)
      (letter_2h2 (car (cdr lis)) 6)
      (if (= (car lis) 3)
          (letter_2h2 (car (cdr lis)) 6)
          (if (= (car lis) 4)
              (letter_2h2 (car (cdr lis)) 6)
              (if (= (car lis) 5)
                  (letter_2h2 (car (cdr lis)) 5)
                  (if (= (car lis) 6)
                      (letter_2h2 (car (cdr lis)) 5)
                      (if (= (car lis) 7)
                          (letter_2h2 (car (cdr lis)) 7)
                          (if (= (car lis) 8)
                              (letter_2h2 (car (cdr lis)) 6)
                              (letter_2h2 (car (cdr lis)) 6)))))))))

(define (letter2 num)
  (letter_2h1 (num-list num)))

(define (letter3 num)
  (letter_2h2 (car (num-list num)) (+ 10 (letter_2h1 (cdr (num-list num))))))

(define (amounth item lis num)
  (if (empty? lis)
      num
      (if (= (car lis) item)
          (amounth item (cdr lis) (+ num 1))
          (amounth item (cdr lis) num))))

(define (amount item lis)
  (amounth item lis 0))

(define (amountvh item vec num on len)
  (if (= len on)
      num
      (if (= (vector-ref vec on) item)
          (amountvh item vec (+ num 1) (+ on 1) len)
          (amountvh item vec num (+ on 1) len))))

(define (amountv item vec)
  (amountvh item vec 0 0 (vector-length vec)))

#|
(define (removeh item lis new)
  (if (empty? lis)
      (rev new)
      (if (= (car lis) item)
          (removeh item (cdr lis) new)
          (removeh item (cdr lis) (cons (car lis) new)))))

(define (remove item lis)
  (removeh item lis (list)))
|#

(define (remove1h item lis new done?)
  (if (empty? lis)
      (rev new)
      (if (and (= (car lis) item) (= done? 0))
          (remove1h item (cdr lis) new 1)
          (remove1h item (cdr lis) (cons (car lis) new) done?))))

(define (remove1 item lis)
  (remove1h item lis (list) 0))

(define (tri?h num on)
  (if (< num 0)
      false
      (if (= num 0)
          true
          (tri?h (- num on) (+ on 1)))))

(define (triangle? num)
  (tri?h num 1))

(define (triangleh num on new)
  (if (= num 0)
      new
      (triangleh (- num 1) (+ on 1) (+ new on))))

(define (triangle num)
  (triangleh num 1 0))

(define (factorer#h pfl found)
  (if (empty? pfl)
      found
      (factorer#h (remove (car pfl) pfl) (* (+ (amount (car pfl) pfl) 1) found))))

(define (factorer# num)
  (factorer#h (pf num) 1))

(define (p#12h on)
  (if (> (factorer# (triangle on)) 500)
      (triangle on)
      (p#12h (+ on 1))))

(define (p#12)
  (p#12h 3))

(define (p#17h num on)
  (if (= on 1000)
      num
      (if (= 2 (length_lis (num-list on)))
          (p#17h (+ num (letter2 on)) (+ on 1))
          (p#17h (+ num (letter3 on)) (+ on 1)))))


(define (p#17)
  (+ 117 (p#17h 0 20)))


(length_lis (list 'o 'n 'e    't 'w 'o   't 'h 'r 'e 'e    'f 'o 'u 'r     'f 'i 'v 'e    's 'i 'x    's 'e 'v 'e 'n    'e 'i 'g 'h 't     'n 'i 'n 'e    't 'e 'n    'e 'l 'e 'v 'e 'n   't 'w 'e 'l 'v 'e    't 'h 'i 'r 't 'e 'e 'n     'f 'o 'u 'r 't 'e 'e 'n    'f 'i 'f 't 'e 'e 'n    's 'i 'x 't 'e 'e 'n    's 'e 'v 'e 'n 't 'e 'e 'n     'e 'i 'g 'h 't 'e 'e 'n     'n 'i 'n 'e 't 'e 'e 'n    'o 'n 'e 't 'h 'o 'u 's 'a 'n 'd))

(define counts-empty (make-immutable-hash '()))

(define (incr-count counts key)
  (hash-set counts key
            (+ 1 (hash-ref counts key 0))))

(define (count-listh l counts)
  (if (empty? l) counts
      (count-listh (cdr l)
                   (incr-count counts (car l)))))

(define (count-list l)
  (count-listh l counts-empty))

(define (p#18h lis has row place)
  (if (> (+ 1 row) (length_lis lis))
      (car lis)
      (if (hash-has-key? has (cons row place))
          (hash-ref has (cons row place))
          (let*
              ([left (p#18h (frontd lis (+ 1 row)) has (+ row 1) (+ place 1))]
               [right (p#18h (frontd lis row) has (+ row 1) place)]
               [answer (+ (car lis) (max left right))]
               )
            (hash-set! has (cons row place) answer)
            answer))))

(define (p#18 lis)
  (p#18h lis (make-hash) 1 1))

(define (func2# funcer arg1 arg2 outt outf)
  (if (funcer arg1 arg2)
      outt
      outf))

(define (daymonth leap day)
  (if (< day 32)
      day
      (if (< day (+ leap 60))
          (- day 31)
          (if (< day (+ leap 91)) 
              (- day (+ leap 59))
              (if (< day (+ leap 121))
                  (- day (+ leap 90))
                  (if (< day (+ leap 152))
                      (- day (+ leap 120))
                      (if (< day (+ leap 182)) 
                          (- day (+ leap 151))
                          (if (< day (+ leap 213)) 
                              (- day (+ leap 181))
                              (if (< day (+ leap 244))
                                  (- day (+ leap 212))
                                  (if (< day (+ leap 274))
                                      (- day (+ leap 243))
                                      (if (< day (+ leap 305)) 
                                          (- day (+ leap 273))
                                          (if (< day (+ leap 335))
                                              (- day (+ leap 304))
                                              (- day (+ leap 334))))))))))))))


(define (p#19h ony ond endy endd amount day)
  (if (and (= ony endy) (= ond endd))
      amount
      (if (or (and (= (daymonth 1 ond) 1) (or (factor 400 ony) (and (factor 4 ony) (not (factor 100 ony))))) (and (= (daymonth 0 ond) 1) (or (not (factor 4 ony)) (and (not (factor 400 ony)) (factor 100 ony)))))
          (if (factor 400 ony)
              (if (= ond 366)
                  (p#19h (+ ony 1) 1 endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1)))
                  (p#19h ony (+ ond 1) endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1))))
              (if (factor 100 ony)
                  (if (= ond 365)
                      (p#19h (+ ony 1) 1 endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1)))
                      (p#19h ony (+ ond 1) endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1))))
                  (if (= 4 ond)
                      (if (= ond 366)
                          (p#19h (+ ony 1) 1 endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1)))
                          (p#19h ony (+ ond 1) endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1))))
                      (if (= ond 365)
                          (p#19h (+ ony 1) 1 endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1)))
                          (p#19h ony (+ ond 1) endy endd (+ amount (func2# = day 7 1 0)) (func2# = day 7 1 (+ day 1)))))))
          (if (factor 400 ony)
              (if (= ond 366)
                  (p#19h (+ ony 1) 1 endy endd amount (func2# = day 7 1 (+ day 1)))
                  (p#19h ony (+ ond 1) endy endd amount (func2# = day 7 1 (+ day 1))))
              (if (factor 100 ony)
                  (if (= ond 365)
                      (p#19h (+ ony 1) 1 endy endd amount (func2# = day 7 1 (+ day 1)))
                      (p#19h ony (+ ond 1) endy endd amount (func2# = day 7 1 (+ day 1))))
                  (if (factor 4 ony)
                      (if (= ond 366)
                          (p#19h (+ ony 1) 1 endy endd amount (func2# = day 7 1 (+ day 1)))
                          (p#19h ony (+ ond 1) endy endd amount (func2# = day 7 1 (+ day 1))))
                      (if (= ond 365)
                          (p#19h (+ ony 1) 1 endy endd amount (func2# = day 7 1 (+ day 1)))
                          (p#19h ony (+ ond 1) endy endd amount (func2# = day 7 1 (+ day 1))))))))))

(define (p#19 starty startd endy endd)
  (p#19h starty startd endy endd 0 1))

(define (fibh num on1 on2)
  (if (= num 1)
      on1
      (fibh (- num 1) (+ on1 on2) on1)))

(define (fib num)
  (fibh num 1 0))

(define (dfib x)
  (cond
    [(<= x 0) 1]
    [else (+ (dfib (- x 1)) 
             (dfib (- x 2)))]))


(define (contains? lis looking)
  (if (empty? lis)
      false
      (if (= looking (car lis))
          true
          (contains? (cdr lis) looking))))

(define (containsl? lis looking)
  (if (empty? lis)
      false
      (if (equal? looking (car lis))
          true
          (containsl? (cdr lis) looking))))

(define (undooph lis new)
  (if (empty? lis)
      (rev new)
      (if (containsl? new (car lis))
          (undooph (cdr lis) new)
          (undooph (cdr lis) (cons (car lis) new)))))

(define (multlh lis num new)
  (if (empty? lis)
      (rev new)
      (multlh (cdr lis) num (cons (* (car lis) num) new))))

(define (multl lis num)
  (multlh lis num (list)))

(define (addlh lis num new)
  (if (empty? lis)
      (rev new)
      (addlh (cdr lis) num (cons (+ (car lis) num) new))))

(define (addl lis num)
  (addlh lis num (list)))

(define (addhh has num new keys)
  (if (empty? keys)
      new
      (addhh has num (hash-set new (+ num (car keys)) (hash-ref has (car keys))) (cdr keys))))

(define (addh num has)
  (addhh has num (make-immutable-hash) (hash-keys has)))

(define (undoop lis)
  (undooph lis (list)))

(define (multallh lis)
  (if (= (length_lis lis) 2)
      (list (car lis) (car (cdr lis)) (* (car lis) (car (cdr lis))))
      (flatten (cons (car lis) (cons (multl (multallh (cdr lis)) (car lis)) (multallh (cdr lis)))))))

(define (multall lis)
  (undoop (multallh lis)))

(define (myand thing1 thing2)
  (if (and thing1 thing2)
      true
      false))

(define (factorer num)
  (multall (flatten (cons 1 (list (pf num))))))

(define (p#21h on lis)
  (if (= on 0)
      lis
      (p#21h (- on 1) (func2# myand (= (sum (remove (sum (remove on (factorer on))) (factorer (sum (remove on (factorer on)))))) on) (not (= on (sum (remove on (factorer on))))) (cons on lis) lis))))

(define (p#21)
  (sum (remove 1 (p#21h 10000 (list)))))

(define (keepmulth lis new)
  (if (empty? lis)
      new
      (if (or (containsl? (cdr lis) (car lis)) (containsl? new (car lis)))
          (keepmulth (cdr lis) (cons (car lis) new))
          (keepmulth (cdr lis) new))))

(define (keepmult lis)
  (keepmulth lis (list)))

(define (keepmultlh lis new)
  (if (empty? lis)
      new
      (if (or (containsl? (cdr lis) (car lis)) (containsl? new (car lis)))
          (keepmulth (cdr lis) (cons (car lis) new))
          (keepmulth (cdr lis) new))))

(define (keepmultl lis)
  (keepmultlh lis (list)))

(define (chimas lis amount things)
  (if (= (length_lis lis) (- amount 1))
      0
      (if (containsl? things (front amount lis))
          amount
          (chimas (cdr lis) amount (cons (front amount lis) things)))))

(define (imash lis amount tobewins)
  (if (= amount 0)
      (list)
      (begin
        (set! tobewins (chimas lis amount (list)))
        (if (= tobewins 0)
            (imash lis (- amount 1) (list))
            tobewins))))

(define (imas lis)
  (imash lis (- (length_lis lis) 1) (list)))

(define (randlh amount high rlis)
  (if (= (length_lis rlis) amount)
      rlis
      (randlh amount high (cons (random (+ high 1)) rlis))))


(define (randl amount high)
  (randlh amount high (list)))

(define (averegeimahh amount highest times lengths)
  (if (= times 0)
      lengths
      (averegeimahh amount highest (- times 1) (cons (imas (randl amount highest)) lengths))))

(define (averegimah amount highest run lengths bla)
  (set! bla (averegeimahh amount highest run (list)))
  (/ (sum bla) (length_lis bla)))

(define (averegeima amount highest run)
  (averegimah amount highest run (list) 0))

(define (abundent? num)
  (> (sum (factorer num)) (* 2 num)))

(define (addpairh lis new on)
  (if (= (+ on 1) (length_lis lis))
      new
      (addpairh lis (flatten (cons (addl (frontd lis (+ on 1)) (car (frontd lis on))) new)) (+ on 1))))

(define (addpair lis)
  (addpairh lis (list) 0))

(define (allabh high new on)
  (if (= on (+ high 1))
      new
      (if (abundent? on)
          (allabh high (cons on new) (+ on 1))
          (allabh high new (+ on 1)))))

(define (allab high)
  (allabh high (list) 11))

(define (nth num lis)
  (if (= num 1)
      (car lis)
      (nth (- num 1) (cdr lis))))

(define (mih)
  (make-immutable-hash))

(define (mmh)
  (make-hash))

(define (addpairhh lis new on len)
  (if (= (+ on 1) len)
      new
      (addpairhh lis)))

(define (addpairl-h lis)
  (addpairhh lis (mih) 0 (length_lis lis)))

(define (all-sums-hh n nums hash)
  (if (empty? nums)
      hash
      (let* ([new-sum (+ n (car nums))]
             [new-hash (if (> new-sum 28123) hash (hash-set hash new-sum '()))])
        (all-sums-hh n (cdr nums) new-hash))))

(define (all-sums-h nums hash)
  (if (empty? nums) 
      hash
      (all-sums-h (cdr nums) (all-sums-hh (car nums) nums hash))))

(define (all-sumsh nums) 
  (all-sums-h nums (make-immutable-hash)))

(define (p#23h on abund new)
  (if (= on 28123)
      (sum new)
      (if (hash-has-key? abund on)
          (p#23h (+ on 1) abund new)
          (p#23h (+ on 1) abund (cons on new)))))

(define (p#23)
  (p#23h 1 (all-sumsh (allab 28123)) (list)))

(define (adde-lh element lis new)
  (if (empty? lis)
      (rev new)
      (adde-lh element (cdr lis) (cons (cons element (car lis)) new))))

(define (adde-l element lis)
  (adde-lh element lis (list)))

(define (insert element lis place)
  (append (front (- place 1) lis) 
          (cons element (frontd lis (- place 1)))))

(define (distibh element lis new on high)
  (if (> on high)
      new
      (distibh element lis (cons (flatten (insert element lis on)) new) (+ on 1) high)))

(define (distrib element lis)
  (distibh element lis (list) 1 (+ 1 (length_lis lis))))

(define (distribsk amount element lis)
  (distibh element lis (list) (+ 1 amount) (+ 1 (length_lis lis))))

(define (applyf-lh func lis new arg)
  (if (empty? lis)
      (rev new)
      (applyf-lh func (cdr lis) (append (func arg lis) new) arg)))

(define (applyf-l1 func lis arg)
  (applyf-lh func lis (list) arg))

(define (applyf-l2h func lis new arg arg2)
  (if (empty? lis)
      (rev new)
      (applyf-l2h func (cdr lis) (append (func arg arg2 (car lis)) new) arg arg2)))

(define (applyf-l2 func lis arg arg2)
  (applyf-l2h func lis (list) arg arg2))

(define (distribplh lis place element new)
  (if (empty? lis)
      (rev new)
      (distribplh (cdr lis) place element (cons (append (front (- place 1) (car lis)) (cons element (frontd (car lis) (- place 1)))) new))))

(define (distribpl lis element place)
  (distribplh lis place element (list)))

(define (23distribh num lis on max new)
  (if (= on (+ 2 max))
      (rev new)
      (23distribh num lis (+ on 1) max (append (distribpl lis num on) new))))

(define (p#23distrib num lis)
  (23distribh num lis 1 (length_lis (car lis)) (list)))

;;(define (applyf-l1-aba func lis arg)
;;  (map (lambda (x) (func x arg)) lis))

(define (allfirh lis new on)
  (if (= on 0)
      new
      (allfirh lis (cons (cons (nth on lis) (remove on lis)) new) (- on 1))))

(define (allfir lis)
  (allfirh lis (list) (length_lis lis)))

;;(define (oneperm lis)
;;  (if (= length_lis 2)
;;      (list  lis (list (cadr lis) (car lis)))

(define (permute lis)
  (if (= (length_lis lis) 2)
      (list lis (list (cadr lis) (car lis)))
      (append
       (p#23distrib (car lis) (permute (cdr lis))))))

(check-expect (permute (list 1 2))
              '((1 2) (2 1)))


(define (p#23case lis1 lis2)
  (if (empty? lis1)
      false
      (if (> (car lis1) (car lis2))
          false
          (if (< (car lis1) (car lis2))
              true
              (p#23case (cdr lis1) (cdr lis2))))))

;(/ (sum (list 7172066 8269263 7284157 6666128 7525122 7013083 6619354 7323310 5757639 6681999 7324069 7267822 7185759 7213099 7235713 7529224 7421067)) 17) 
;(/ (sum (list 1290502 7557141 2310230 3161290 6776354 6171961 5056629 3133445 647453 6509999 1858560 6436591 5500821 6171614 1488636 6175351 6431453)) 17)

(define (fibdigh num last twolast on)
  (if (= (length_lis (num-list (+ last twolast))) num)
      on
      (fibdigh num (+ last twolast) last (+ on 1))))

(define (fibdig num)
  (fibdigh num 1 1 3))

(define (rept#<1hl num den stored on qout floo digits)
  (set! qout (/ (list-num (num-list num)) den))
  (set! floo (floor qout))
  (if (hash-has-key? stored floo)
      (- on (hash-ref stored floo))
      (if (= qout 1)
          0
          (if (= floo 0)
              (rept#<1hl (* num 10) den stored (+ on 1) 0 0 (+ digits 1))
              (rept#<1hl (* (- num (* den floo)) 10) den (hash-set stored (remainder num den) on) (+ on 1) 0 0 1)))))

(define (rept#<1l num den)
  (rept#<1hl num den (mih) 1 0 0 1))

(define (2s5s num)
  (empty? (remove 5 (remove 2 (flatten (list (pf num)))))))

(define (fracrepth num den on)
  (if (or (2s5s (denominator (- (* (expt 10 on) (/ num den)) (/ num den)))) (integer? (- (* (expt 10 on) (/ num den)) (/ num den))))
      on 
      (fracrepth num den (+ on 1))))

(define (fracrept num den)
  (define l (remove 5 (remove 2 (flatten (list (pf den))))))
  (if (empty? l)
      0
      (fracrepth num den 1)))

(define (p#26h on ma ma#)
  (if (> on 999)
      ma#
      (if (> ma (fracrept 1 on))
          (p#26h (+ on 1) ma ma#)
          (p#26h (+ on 1) (fracrept 1 on) on))))

(define (rtrue x)
  true)

(define (p#26)
  (p#26h 2 0 1))

(define (true? bool)
  (if bool
      true
      false))

(define (sivhh vec on len add)
  (if (> (+ 1 on) len)
      '()
      (begin
        (vector-set! vec on false)
        (sivhh vec (+ on add) len add))))

(define (posval x)
  (max (- 0 x) x))

(define (sivh vec on ma)
  (if (> on (- (/ ma 2) 1))
      vec
      (if (eq? true (vector-ref vec on))
          (begin
            (sivhh vec (* 2 on) ma on) 
            (sivh vec (+ on 1) ma))
          (sivh vec (+ on 1) ma))))

(define (siv max)
  (let ([vec (build-vector max rtrue)])
    (begin
      (sivh vec 2 max)
      (vector-set! vec 0 false)
      (vector-set! vec 1 false)
      vec)))

(define (euformh a b on)
  (if (eq? (vector-ref p (posval (+ (expt on 2) (* on a) b))) false)
      on
      (euformh a b (+ on 1))))

(define (euform a b)
  (euformh a b 0))

(define (p#27h- a b bigval bigprod nums ans)
  (if (and (= a -1000) (< b -997))
      bigprod
      (begin
        (set! ans (euform a b))
        (if (< b -997)
            (if (> ans bigval)
                (p#27h- (- a 1) 997 ans (* a b) (cons a b) 0)
                (p#27h- (- a 1) 997 bigval bigprod nums 0))
            (if (> ans bigval)
                (p#27h- a (- b 1) ans (* a b) (cons a b) 0)
                (p#27h- a (- b 1) bigval bigprod nums 0))))))

(define (p#27)
  (p#27h- 1000 997 0 0 0 (cons 0 0)))

(define (p#28h maxlay layer accum last)
  (if (= layer maxlay)
      accum
      (p#28h maxlay (+ layer 1) (+ accum (+ (* 4 last) (* layer 20))) (+ last (* 8 layer)))))

(define (p#28 layers)
  (p#28h layers 1 1 1))

(define (p#29h has base exp ma)
  (if (and (= base ma) (= exp ma))
      has
      (if (= exp ma)
          (p#29h (hash-set has (expt base exp) (list)) (+ base 1) 2 ma)
          (p#29h (hash-set has (expt base exp) (list)) base (+ exp 1) ma))))

(define (p#29 ma)
  (hash-count (p#29h (mih) 2 2 ma)))

(define (p#30h lis on)
  (if (= on 354294)
      lis
      (if (= (sum (map (lambda (x) (expt x 5)) (num-list on))) on)
          (p#30h (cons on lis) (+ on 1))
          (p#30h lis (+ on 1)))))

(define (p#30)
  (sum (p#30h (list) 10)))

(define (onifh lis cond new)
  (if (empty? lis)
      (rev new)
      (if (cond (car lis))
          (onifh (cdr lis) cond (cons (car lis) new))
          (onifh (cdr lis) cond new))))

(define (onif lis cond)
  (onifh lis cond (list)))

(define (onifvh vec cond new on len)
  (if (= len on)
      new
      (if (cond (vector-ref vec on))
          (onifvh vec cond (vector-append (vector (vector-ref vec on)) new) (+ on 1) len)
          (onifvh vec cond new (+ on 1) len))))

(define (onifv vec cond)
  (onifvh vec cond (vector) 0 (vector-length vec)))

(define (apply2h func lis1 lis2 new)
  (if (empty? lis1)
      new
      (apply2h func (cdr lis1) lis2 (append new (map (lambda (x) (func (car lis1) x)) lis2)))))

(define (apply2 func lis1 lis2)
  (apply2h func lis1 lis2 (list)))

(define (apply2v func vec1 vec2)
  (for*/vector ([x vec1]
                [y vec2])
    (func x y)))

(define (p#31h vec on)
  (if (= on 7)
      (vector 0)
      (vector-filter
       (lambda (x) (< x 201))
       (apply2v
        +
        (let*
            ([cost-of-this-coin (vector-ref vec on)]
             [uses-of-this-coin (build-vector (+ 1 (/ 200 cost-of-this-coin)) values)]
             )
          (vector-map (lambda (x) (* x cost-of-this-coin)) uses-of-this-coin))
        (p#31h vec (+ on 1))))))


(define (p#31)
  (amountv 200 (p#31h (vector 200 100 50 20 5 2 1) 0)))


(define (p#6purp on)
  (if (and (= (sum (num-list on)) 27) (not (integer? (/ on 27))))
      on
      (p#6purp (+ on 1))))

(define (p#13purp a b c max maxl)
  (if (and (and (= a 4) (= b 4)) (= c 4))
      maxl
      (begin
        (if (> (+ (expt (+ a (* 2 b) (* 3 c)) 2) (expt (+ b (* 2 c) (* 3 a)) 2) (expt (+ c (* 2 a) (* 3 b)) 2)) max)
            (begin
              (set! maxl (list a b c))
              (set! max (+ (expt (+ a (* 2 b) (* 3 c)) 2) (expt (+ b (* 2 c) (* 3 a)) 2) (expt (+ c (* 2 a) (* 3 b)) 2))))
            (set! max max))
        (if (and (= b 4) (= c 4))
            (p#13purp (+ a 1) -4 -4 max maxl)
            (if (= c 4)
                (p#13purp a (+ b 1) -4 max maxl)
                (p#13purp a b (+ c 1) max maxl))))))

(define (p#19purp a b c d max)
  (if (and (and (and (= a max) (= b max)) (= c max)) (= d max))
      0
      (if (= (+ (expt a 2) (* 3 (expt b 2)) (/ (+ (expt c 2) (* 3 (expt d 2))) 2)) (+ a b c d -1))
          (+ (* 1000 a) (* 100 b) (* 10 c) d)
          (if (and (and (= d max) (= c max)) (= b max))
              (p#19purp (+ a 1) (- 0 max) (- 0 max) (- 0 max) max)
              (if (and (= c max) (= d max))
                  (p#19purp a (+ b 1) (- 0 max) (- 0 max) max)
                  (if (= d max)
                      (p#19purp a b (+ c 1) (- 0 max) max)
                      (p#19purp a b c (+ d 1) max)))))))

(define (1rot lis)
  (append (cdr lis) (list (car lis))))

(define (rotateh on lis end)
  (if (equal? on end)
      lis
      (rotateh (1rot on) (cons (list-num on) lis) end)))

(define (rotate num)
  (rotateh (1rot (num-list num)) (list num) (num-list num)))

(define (rotateph on end)
  (if (equal? on end)
      true
      (if (prime? (list-num on))
          (rotateph (1rot on) end)
          false)))

(define (rotatep? num)
  (if (prime? num)
      (rotateph (1rot (num-list num)) (num-list num))
      false))

(define (amount36h num thing on)
  (if (> 1 (/ num thing))
      on
      (amount36h (/ num thing) thing (+ on 1))))

(define (amount36 num thing)
  (amount36h num thing 1))

(define (baseconvh base10 newbase lis)
  (if (< base10 newbase)
      (list->num (cons base10 lis))
      (baseconvh (quotient base10 newbase)
                 newbase 
                 (cons (remainder base10 newbase) lis))))

(define (baseconv base10 newbase)
  (baseconvh base10 newbase (list)))

(define (z x)
  (length (map (lambda (x) (baseconv x 2)) (range 1 x))))

(define (baseconv-aba x base)
  (if (< x base) x
      (let
          ([q (quotient x base)]
           [r (remainder x base)])
        (+ r (* base (baseconv-aba r base))))))

(define (p#36h on sum)
  (if (= on 1000000)
      sum
      (if (pal? on)
          (if (pal? (baseconv on 2))
              (p#36h (+ on 1) (+ on sum))
              (p#36h (+ on 1) sum))
          (p#36h (+ on 1) sum))))


(define (p#36)
  (p#36h 1 0))

(define (p#37l? lis)
  (if (empty? (cdr lis))
      (if (prime? (car lis))
          true
          false)
      (if (prime? (list->num lis))
          (p#37l? (cdr lis))
          false)))

(define (p#37r? lis)
  (if (empty? (cdr lis))
      (if (prime? (car lis))
          true
          false)
      (if (prime? (list->num lis))
          (p#37r? (drop lis))
          false)))

(define (p#37? num)
  (if (p#37l? (num-list num))
      (if (p#37r? (num-list num))
          true
          false
          )
      false))

(define (p#37h on lis)
  (if (= (length_lis lis) 11)
      (sum lis)
      (if (p#37? on)
          (p#37h (+ on 1) (cons on lis))
          (p#37h (+ on 1) lis))))

(define (p#37)
  (p#37h 10 (list)))

(define (p#38h? num lis on)
  (if (> (length_lis lis) 8)
      (if (equal? (list 1 2 3 4 5 6 7 8 9) (sort lis <))
          (list->num lis)
          0)
      (p#38h? num (append lis (num-list (* num on))) (+ on 1))))

(define (p#38? num)
  (p#38h? num (list) 1))

(define (rtriangle? a b c)
  (and (= (+ (expt a 2) (expt b 2)) (expt c 2)) (and (< a b) (< b c))))

(define (p#39erh num a b c amount)
  (if (and (= (floor (/ (- num a) 2)) b) (= (floor (/ num 3)) a))
      amount
      (if (= b (floor (/ (- num a) 2)))
          (if (rtriangle? c b a)
              (p#39erh num (- a 1) (- num a) 1 (+ amount 1))
              (p#39erh num (- a 1) (- num a) 1 amount))
          (if (rtriangle? c b a)
              (p#39erh num a (- b 1) (+ c 1) (+ amount 1))
              (p#39erh num a (- b 1) (+ c 1) amount)))))

(define p (siv 2)) ;;deletable


(define (p#39er num)
  (p#39erh num (- num 2) 1 1 0))

(define (p#39h on biggestv biggestn randomthing)
  (if (= on 1000)
      biggestn
      (begin
        (set! randomthing (p#39er on))
        (if (> randomthing biggestv)
            (p#39h (+ on 1) randomthing on 0)
            (p#39h (+ on 1) biggestv biggestn 0)))))

(define (p#39)
  (p#39h 10 0 0 0))

(define (p#40hh on lis)
  (if (= on 0)
      lis
      (p#40hh (- on 1) (append (num-list on) lis))))

(define (p#40h something)
  (set! something (p#40hh 300000 (list)))
  (* (nth 1 something)
     (nth 10 something)
     (nth 100 something)
     (nth 1000 something)
     (nth 10000 something)
     (nth 100000 something)
     (nth 1000000 something)))

(define (p#40)
  (p#40h 0))

(define (pand? amount num)
  (equal? (range 1 amount) (sort (num-list num) <)))

(define (p#41h lis max something)
  (if (empty? lis)
      max
      (begin
        (set! something (list-num (car lis)))
        (if (prime? something)
            (if (> something max)
                (p#41h (cdr lis) something 0)
                (p#41h (cdr lis) max 0))
            (p#41h (cdr lis) max 0)))))


(define (p#41)
  (p#41h (permute (list 1 2 3 4 5 6 7)) 0 0))

(define (p#42hh? n3 n4 n5 n6 n7 n8 n9 n10)
  (if (integer? (/ n4 2)) 
      (if (integer? (/ (+ n3 n4 n5) 3)) 
          (if (or (= n6 0) (= n6 5))
              (if (integer? (/ (list->num (list n5 n6 n7)) 7))
                  (if (integer? (/ (list->num (list n6 n7 n8)) 11))
                      (if (integer? (/ (list->num (list n7 n8 n9)) 13))
                          (if (integer? (/ (list->num (list n8 n9 n10)) 17))
                              true
                              false)
                          false)
                      false)
                  false)
              false)
          false)
      false))

(define (p#42h? lis)
  (p#42hh? (nth 1 lis) (nth 2 lis) (nth 3 lis) (nth 4 lis) (nth 5 lis) (nth 6 lis) (nth 7 lis) (nth 8 lis)))

(define (p#42? num)
  (p#42h? (cddr (num-list num))))

(define (pent num)
  (/ (- (* 3 (expt num 2)) num) 2))

(define (penth? num on thing)
  (if (= num thing)
      true
      (if (< num thing)
          false
          (penth? num (+ on 1) (pent on)))))

(define (pent? num)
  (penth? num 2 1))

(define (p#44erh num lis lis+ lis-)
  (if (empty? lis+)
      (list false (list 0 0))
      (if (and (pent? (car lis+)) (pent? (car lis-)))
          (list true (list num (car lis)))
          (p#44erh num (cdr lis) (cdr lis+) (cdr lis-)))))

(define (p#44er num lis)
  (p#44erh num lis (map (lambda (x) (+ num x)) lis) (map (lambda (x) (- num x)) lis)))

(define (p#44h lis on penterer)
  (if (eq? (car (p#44er penterer lis)) true)
      (cdr (p#44er penterer lis))
      (p#44h (cons penterer lis) (+ on 1) (pent on))))

(define (p#44)
  (car (p#44h (list 1) 3 5)))

#|

(define (small-listh lis smallest)
  (if (empty? lis)
      small
      (if (or (equal? smallest '()) (> smallest (car lis)))
          (small-listh (cdr lis) (car lis))
          (small-listh (cdr lis) smallest))))

(define (small-list lis)
  (small-listh lis '()))

(define (pref-voth coices votes smallest)
  (set! smallest (small-list (flatten votes))

(define (pref-vot choices votes)
  (perf-voth choices votes 0))

|#

(define (distinct_itemsh lis new)
  (if (empty? lis)
      (reverse new)
      (if (contains? new (car lis))
          (distinct_itemsh (cdr lis) new)
          (distinct_itemsh (cdr lis) (cons (car lis) new)))))

(define (distinct_items lis)
  (distinct_itemsh lis (list)))

(define (distinct_items# lis)
  (length (distinct_items lis)))

(define (pf# n)
  (if (integer? (pf n))
      1
      (distinct_items# (pf n))))

(define (p47h on count)
  (if (= count 4)
      (- on 3)
      (if (= (pf# on) 4)
          (p47h (+ on 1) (+ count 1))
          (p47h (+ on 1) 0))))

(define (p47)
  (p47h 0 0))

(define (power base exponet)
  (if (= exponet 0)
      1
      (* base (power base (- exponet 1)))))

(define (adding_self_powersh x count)
  (if (= x 0)
      count
      (adding_self_powersh (- x 1) (+ count (power x x)))))

(define (adding_self_powers x)
  (adding_self_powersh x 0))

(define (primes_beth on largest l)
  (if (> on largest)
      (reverse l)
      (if (prime? on)
          (primes_beth (+ on 1) largest (cons on l))
          (primes_beth (+ on 1) largest l))))

(define (primes_bet lowest largest)
  (primes_beth lowest largest (list)))

(define (vector->listh r on v-length)
  (if (= on v-length)
      (list)
      (if (vector-ref r on)
          (cons on (vector->listh r (+ on 1) v-length))
          (vector->listh r (+ on 1) v-length))))

(define (vector->list r)
  (vector->listh r 1 (vector-length r)))

(define (primes_upto highest)
  (vector->list (siv highest)))

(define (primes_between lowest highest)
  (remove 0 (map (lambda (x) (if (< x lowest) 0 x)) (primes_upto highest))))

(define (similar?#h l1 l2)
  (if (empty? l1)
      true
      (if (contains? l2 (car l1))
          (similar?#h (cdr l1) (remove1 (car l1) l2))
          false)))

(define (similar?# l1 l2)
  (if (= (length l1) (length l2))
      (similar?#h l1 l2)
      false))

(define (all_similar# l1 lis)
  (if (empty? lis)
      (list)
      (if (similar?# l1 (car lis))
          (cons (car lis) (all_similar# l1 (cdr lis)))
          (all_similar# l1 (cdr lis)))))

(define (arithmetic?h l dif)
  (if (= (length l) 1)
      true
      (if (= (- (cadr l) (car l)) dif)
          (arithmetic?h (cdr l) dif)
          false)))

(define (arithmetic? l)
  (arithmetic?h (cdr l) (- (cadr l) (car l))))

(define (where# num l)
  (if (= (car l) num)
      1
      (+ 1 (where# num (cdr l)))))

(define (p#49h primes setter)
  (if (empty? primes)
      (list)
      (begin
        (set! setter (map (lambda (x) (if (> (length x) 2) (if (arithmetic? (map (lambda (y) (list->num y)) (front 3 x))) 1 0) 0)) (map (lambda (x) (map (lambda (y) (num-list y)) x) (permute (map (lambda (x) (list->num x)) (all_similar# (car primes) primes)))))))
        (if (contains? setter 1)
            (cons (nth (where# 1 setter) (permute (all_similar# (car primes) primes))) (p#49h (cdr primes) 0))
            (p#49h (cdr primes) 0)))))

(define (p#49)
  (p#49h (map (lambda (x) (num-list x)) (primes_bet 1000 9999)) 0))

;;(define primes (map (lambda (x) (num-list x)) (primes_bet 1000 9999)))

(define (set_sum len start l)
  (sum (front len (frontd l (- start 1)))))

(define (all_set_sum_length len l)
  (if (< (length l) len)
      (list)
      (cons (set_sum len 1 l) (all_set_sum_length len (cdr l)))))

(define (p#50h primesl on setter)
  (if (= on 1)
      (list)
      (begin
        (set! setter (remove 0 (map (lambda (x) (if (< x 1000000) (if (prime? x) x 0) 0)) (all_set_sum_length on primesl))))
        (if (not (empty? setter))
            setter
            (p#50h primesl (- on 1) 0)))))

(define (p#50 primesl)
  (p#50h primesl (length primesl) 0))

(define (permutations?h l1 l2)
  (if (empty? l1)
      true
      (if (contains? l2 (car l1))
          (permutations?h (cdr l1) (remove1 (car l1) l2))
          false)))

(define (permutations?st l1 l2)
  (if (= (length l1) (length l2))
      (permutations?h l1 l2)
      false))

(define (permutations? n1 n2)
  (permutations?st (num-list n1) (num-list n2)))

(define (p#52? n)
  (and (permutations? n (* n 2)) (permutations? n (* n 2)) (permutations? n (* n 3)) (permutations? n (* n 4)) (permutations? n (* n 5)) (permutations? n (* n 6))))

(define (p#52 on)
  (if (p#52? on)
      on
      (p#52 (+ on 1))))

(define (p#53hh first on)
  (if (> on first)
      0
      (if (> (choose first on) 1000000)
          (+ 1 (p#53hh first (+ on 1)))
          (p#53hh first (+ on 1)))))

(define (p#53h on)
  (if (> on 100)
      0
      (+ (p#53hh on 1) (p#53h (+ on 1)))))

(define (p#53)
  (p#53h 20))

(define (lychrel?h n times)
  (if (pal? n)
      false
      (if (> times 50)
          true
          (lychrel?h (+ n (list->num (reverse (num-list n)))) (+ times 1)))))

(define (lychrel? n)
  (lychrel?h (+ n (list->num (reverse (num-list n)))) 2))

(define (p? n)
  (if (< n 2000001)
      (if (= n 1)
          false
          (vector-ref p (- n 1)))
      (prime? n)))

(define (p#55 on)
  (if (> on 10000)
      0
      (if (lychrel? on)
          (+ 1 (p#55 (+ on 1)))
          (p#55 (+ on 1)))))

(define (dig_sum n)
  (sum (num-list n)))

(define (p#56 a b)
  (if (= a 99)
      (if (= b 99)
          0
          (max (dig_sum (power a b)) (p#56 a (+ b 1))))
      (if (= b 99)
          (max (dig_sum (power a b)) (p#56 (+ a 1) 1))
          (max (dig_sum (power a b)) (p#56 a (+ b 1))))))

(define (diags_toh highest on adding corner)
  (if (> on highest)
      (list)
      (if (= corner 4)
          (cons on (diags_toh highest (+ on adding) (+ adding 2) 1))
          (cons on (diags_toh highest (+ on adding) adding (+ corner 1))))))

(define (diags_to highest)
  (diags_toh highest 1 2 1))

(define (on_diag?h n on adding corner)
  (if (> on n)
      false
      (if (= on n)
          true
          (if (= corner 4)
              (on_diag?h n (+ on adding) (+ adding 2) 1)
              (on_diag?h n (+ on adding) adding (+ 1 corner))))))

(define (on_diag? n)
  (on_diag?h n 1 2 1))

(define (percent_primesh l times amount primesl)
  (if (empty? l)
      (/ amount times)
      (if (contains? primesl (car l))
          (percent_primesh (cdr l) (+ 1 times) (+ amount 1) primesl)
          (percent_primesh (cdr l) (+ 1 times) amount primesl))))

(define (diagsh limit on)
  (if (> on limit)
      (list)
      (if (on_diag? on)
          (cons on (diagsh limit (+ on 1)))
          (diagsh limit (+ on 1)))))

(define (diags limit)
  (diagsh limit 1))

(define (percent_primes l)
  (percent_primesh l 0 0 p))

(define (primes_inh l times)
  (if (empty? l)
      times
      (if (prime? (car l))
          (primes_inh (cdr l) (+ 1 times))
          (primes_inh (cdr l) times))))

(define (primes_in l)
  (primes_inh l 0))

(define (p#58h on primes# amount setter)
  (if (< (/ primes# amount) 1/10)
      (list primes# amount)
      (begin
        (set! setter (diags_toh (* (+ 2 on) (+ 2 on)) (+ (* on on) 1 on) (+ on 1) 1))
        (p#58h (+ on 2) (+ primes# (primes_in setter)) (+ amount 4) 0))))

(define (p#58 on primes# amount)
  (p#58h on primes# amount 0))

#|
(define (2set? x y)
  (and (p? (list->num (append (num-list x) (num-list y)))) (p? (list->num (append (num-list y) (num-list x))))))

(define (p#60?h l len)
  (if (= len 2)
      (2set? (car l) (cadr l))
      (and (p#60?h (cdr l) (- len 1)) (not (contains? (map (lambda (x) (if (2set? (car l) x) 0 1)) (cdr l)) 1)))))

(define (p#60? l)
  (if (contains? (map (lambda (x) (if (prime? x) 0 1)) l) 1)
      false
      (p#60?h l (length l))
      ))

(define (p#60pairsh first l)
  (if (empty? l)
      (list)
      (if (2set? first (car l))
          (cons (list first (car l)) (p#60pairsh first (cdr l)))
          (p#60pairsh first (cdr l)))))

(define (p#60pairser l)
  (if (empty? l)
      (list)
      (append (p#60pairsh (car l) (cdr l)) (p#60pairser (cdr l)))))

(define (p#60pairs l)
  (remove (list) (undoop (p#60pairser l))))

(define (p#60listh prime l)
  (if (empty? l)
      (list)
      (if (contains? (map (lambda (x) (if (2set? (car x) (cadr x)) 1 0))
                          (map (lambda (x) (list prime x))
                               (car l))) 0)
          (p#60listh prime (cdr l))
          (append (cons prime (car l)) (p#60listh prime (cdr l))))))

(define (p#60lister primes l)
  (if (empty? primes)
      (list)
      (cons (p#60listh (car primes) l) (p#60lister (cdr primes) l))))

(define (p#60list primes l)
  (remove (list) (undoop (p#60lister primes l))))

(define (p#60lenh len l primes)
  (if (= len 1)
      l
      (p#60lenh (- len 1) (p#60list primes l) primes)))

(define (p#60len len primes)
  (p#60lenh (- len 1) (p#60pairs primes) primes))
(printf "~s" last)

(define (p#60h on l max)
  (if (empty? l)
      (p#60h (* on 2) (p#60len 5 (cdr (vector->list (siv on)))))
      (if (> on max)
          (list l (p#60len 5 (cdr (vector->list (siv (large_list l))))))

(define (p#60)
  (p#60h 1000 (list) 0))
|#

(define (p#61P base n)
  (/ (* n (+ (* n (- base 2)) (- 4 base))) 2))

(define (p#61numbers base on last vectorer max)
  (if (> last max)
      vectorer
      (if (< (p#61P base on) max)
          (begin
            (vector-set*! vectorer (p#61P base on) true)
            (p#61numbers base (+ on 1) (p#61P base on) vectorer max))
          (p#61numbers base (+ on 1) (p#61P base on) vectorer max))))

(define (mod. num base)
  (if (< num base)
      num
      (mod. (- num base) base)))

#|
(define 61nums3 (p#61numbers 3 2 1 (make-vector 11000 false) 10000))
(define 61nums4 (p#61numbers 4 2 1 (make-vector 11000 false) 10000))
(define 61nums5 (p#61numbers 5 2 1 (make-vector 11000 false) 10000))
(define 61nums6 (p#61numbers 6 2 1 (make-vector 11000 false) 10000))
(define 61nums7 (p#61numbers 7 2 1 (make-vector 11000 false) 10000))
(define 61nums8 (p#61numbers 8 2 1 (make-vector 11000 false) 10000))


(define (p#61? base num)
  (cond
    [(= base 3) (vector-ref 61nums3 num)]
    [(= base 4) (vector-ref 61nums4 num)]
    [(= base 5) (vector-ref 61nums5 num)]
    [(= base 6) (vector-ref 61nums6 num)]
    [(= base 7) (vector-ref 61nums7 num)]
    [(= base 8) (vector-ref 61nums8 num)]))


(define (p#61?l l)
  (=
   (/ (- (car l) (mod. (car l) 100)) 100)
   (mod. (last l) 100)))

(define (p#61?ll l)
  (if (and (not (empty? (car l))) (p#61?l (car l)))
      (car l)
      (p#61?ll (cdr l))))

(define (p#61)
  (p#61?ll (p#61A (permute (list 3 4 5 6 7 8)))))

(define (p#61A permutations)
  (if (empty? permutations)
      (list)
      (append (p#61a 10 (car permutations)) (p#61A (cdr permutations)))))

(define (p#61a on order)
  (if (= on 100)
      (list)
      (if (= (length (p#61h on 1 0 order)) 6)
          (cons (p#61h on 1 10 order) (p#61a (+ on 1) order))
          (p#61a (+ on 1) order))))

(define (p#61h num phase on order)
  (cond
    [(= on 100) (list)]
    [(= phase 1) (if (p#61? (nth phase order) (+ (* 100 num) on))
                     (cons (+ (* 100 num) on) (p#61h on (+ phase 1) 10 order))
                     (p#61h num phase (+ on 1) order))]
    [(= phase 2) (if (p#61? (nth phase order) (+ (* 100 num) on))
                     (cons (+ (* 100 num) on) (p#61h on (+ phase 1) 10 order))
                     (p#61h num phase (+ on 1) order))]
    [(= phase 3) (if (p#61? (nth phase order) (+ (* 100 num) on))
                     (cons (+ (* 100 num) on) (p#61h on (+ phase 1) 10 order))
                     (p#61h num phase (+ on 1) order))]
    [(= phase 4) (if (p#61? (nth phase order) (+ (* 100 num) on))
                     (cons (+ (* 100 num) on) (p#61h on (+ phase 1) 10 order))
                     (p#61h num phase (+ on 1) order))]
    [(= phase 5) (if (p#61? (nth phase order) (+ (* 100 num) on))
                     (cons (+ (* 100 num) on) (p#61h on (+ phase 1) 10 order))
                     (p#61h num phase (+ on 1) order))]
    [(= phase 6) (if (p#61? (nth 6 order) (+ (* 100 num) on))
                     (list (+ (* 100 num) on))
                     (p#61h num phase (+ on 1) order))]))
|#

(define (p#62l on l max)
  (if (= on max)
      l
      (p#62l (+ on 1) (cons (power on 3) l) max)))

#|
(define 8dcubes (p#62l 216 (list) 465))
(define 9dcubes (p#62l 465 (list) 1000))
(define 10dcubes (p#62l 1000 (list) 2155))
(define 11dcubes (p#62l 2155 (list) 4642))
|#

(define (dcubes digits)
  (p#62l (ceiling (expt (expt 10 (- digits 1)) 1/3))
         (list)
         (ceiling (expt (expt 10 digits) 1/3))))

(define (p#62 phase last cubes)
;;  (printf "~s" phase)
  (if (not (or (= phase 1) (= phase 6) (empty? cubes)))
      (if (and
           (permutations? last (car cubes))
           (list? (p#62 (+ phase 1) last (cdr cubes))))
          (cons (car cubes) (p#62 (+ phase 1) last (cdr cubes)))
          (p#62 phase last (cdr cubes)))
      (cond
        [(= phase 6) (list)]
        [(empty? cubes) false]
        [(= phase 1) (if (list? (p#62 2 (car cubes) (cdr cubes)))
                         (begin
                           (printf "~s" (car cubes))
                           (cons (car cubes) (p#62 2 (car cubes) (cdr cubes))))
                         (p#62 1 0 (cdr cubes)))])))


(define (p#63 base exp)
  (if (= exp 1000)
      (list)
      (if (= (floor (+ .0000000001 (/ (log (expt base exp)) (log 10)))) (- exp 1))
          (cons (cons base (cons exp (expt base exp))) (p#63 (+ base 1) exp))
          (if (>= (floor (+ .0000000001 (/ (log (expt base exp)) (log 10)))) exp)
              (p#63 1 (+ exp 1))
              (p#63 (+ base 1) exp)))))

(define (squares vec on max)
  (if (> on max)
      vec
      (if (square-number? on)
          (begin
            (vector-set! vec on true)
            (squares vec (+ on 1) max))
          (squares vec (+ on 1) max))))

(define (pfcounting pfs originals)
  (if (empty? pfs)
      (list)
      (if (= (car pfs) 1)
          (cons (car originals) (pfcounting (cdr pfs) (cdr originals)))
          (cons (- (car pfs) 1) (pfcounting (cdr pfs) (cdr originals))))))

(define (t-speed func times)
  (if (= times 0)
      0
      (begin
        func
        (t-speed func (- times 1)))))

(define (p#66n num on)
  (if (integer? (sqrt (+ 1 (* num on on))))
      (sqrt (+ 1 (* num on on)))
      (p#66n num (+ on 1))))

(define (p#66n2 num on sqr)
      (if (= (expt (exact-ceiling (* on sqr)) 2) (+ 1 (* num on on)))
          (list on (exact-ceiling (* on sqr)))
          (p#66n2 num (+ on 1) sqr)))

(define (p#66 maxer on best)
  (printf "~s" (list maxer on best))
  (if (= on 1000)
      max
      (if (and (prime? on) (> (p#66n on 1) maxer))
          (p#66 (p#66n on 1) (+ on 1) on)
          (p#66 maxer (+ on 1) best))))

(define (p#67h l)
  (if (empty? l)
      (list)
      (if (=
           (+ (nth 1 (car l)) (nth 6 (car l)) (nth 7 (car l)))
           (+ (nth 2 (car l)) (nth 7 (car l)) (nth 8 (car l)))
           (+ (nth 3 (car l)) (nth 8 (car l)) (nth 9 (car l)))
           (+ (nth 4 (car l)) (nth 9 (car l)) (nth 10 (car l)))
           (+ (nth 5 (car l)) (nth 10 (car l)) (nth 6 (car l))))
          (cons (car l) (p#67h (cdr l)))
          (p#67h (cdr l)))))
#|
(define (p#67sort l)
  (if (= (length l) 2)
      (if (> (caar l) (cdaar l))
          (list
           (cdar l)
           (car l))
          l)
|#      

(define (p#67)
  (map (lambda (x)
;;         (p#67sort
          (list (list (nth 1 x) (nth 6 x) (nth 7 x))
                (list (nth 2 x) (nth 7 x) (nth 8 x))
                (list (nth 3 x) (nth 8 x) (nth 9 x))
                (list (nth 4 x) (nth 9 x) (nth 10 x))
                (list (nth 5 x) (nth 10 x) (nth 6 x))))
         (p#67h (permute (list 1 2 3 4 5 6 7 8 9 10)))))

(define (producth l prod)
  (if (empty? l)
      prod
      (producth (cdr l) (* (car l) prod))))

(define (product l)
  (producth l 1))

(define (p#69s on)
  (product
   (map (lambda (x)
          (/ x (- x 1)))
        (undoop (pf on)))))

(define (p#69pl on ha)
  (if (= on 1000000)
      ha
      (if (prime? on)
          (begin
            (hash-set! ha on (/ on (- on 1)))
            (p#69pl (+ on 1) ha))
          (p#69pl (+ on 1) ha))))

(define (p#69h on maximum biggest)
  (if (= on 1000001)
      biggest
      (if (prime? on)
          (if (> (/ on (- on 1)) maximum)
              (p#69h (+ on 1) (/ on (- on 1)) on)
              (p#69h (+ on 1) maximum biggest))
          (if (> (p#69s on) maximum)
              (p#69h (+ on 1) (p#69s on) on)
              (p#69h (+ on 1) maximum biggest)))))
      

(define (p#69)
  (p#69h 4 0 0))

(define (next n v)
  (if (vector-ref v (+ n 1))
      (+ n 1)
      (next (+ n 1) v)))

(define (before n v)
  (if (vector-ref v (- n 1))
      (- n 1)
      (before (- n 1) v)))

(define (p#70s n)
  (/ n (p#69s n)))

(define (p#70s? n)
  (permutations?
   (p#70s n)
   n))

(define (p#70sort x y)
  (> (cdr x) (cdr y))
  x
  y)

(define (p#70hh num on ps l)
  (if (> num 3162) 
      l
      (if (> (* on num) 9999991)
          (p#70hh (next num ps) 2 ps l)
          (if (not (= on num))
              (p#70hh num (next on ps) ps (cons (cons (* on num) (/ (* on num) (* (/ on (- on 1)) (/ num (- num 1))))) l))
              (p#70hh num (next on ps) ps (cons (cons (* on num) (/ (* on num) (* (/ on (- on 1))))) l))))))

(define (p#70h l small)
  (if (empty? l)
      small
      (if (< (/ (caar l) (cdar l)) small)
          (if (permutations? (caar l) (cdar l))
              (p#70h (cdr l) (car l))
              (p#70h (cdr l) small))
          (p#70h (cdr l) small))))

(define (p#70)
  (p#70h (reverse (sort (p#70hh 2 2 (siv 10000000) (list)) p#70sort)) 2))

(define (p#72 on ps count)
  (if (= on 1000001)
      count
      (if (vector-ref ps on)
          (p#72 (+ on 1) ps (+ count (- on 1)))
          (p#72 (+ on 1) ps (+ count (p#70s on))))))
#|
(define !loops (make-hash (list
                           (cons 1 1)
                           (cons 2 1)
                           (cons 145 1)
                           (cons 169 3)
                           (cons 363601 3)
                           (cons 1454 3)
                           (cons 871 2)
                           (cons 872 2)
                           (cons 45361 2)
                           (cons 45362 2)
                           (cons 40585 1))))

(define dfact
  (vector
   1
   1
   2
   6
   24
   120
   720
   5040
   40320
   362880))

(define (p#74hh l)
  (sum (map
        (lambda (x) (vector-ref dfact x))
        l)))

(define (p#74h on)
  (if (hash-has-key? !loops on)
      (hash-ref !loops on)
      (begin
        (p#74h (p#74hh (num-list on)))
        (hash-set! !loops on (+ 1 (hash-ref !loops (p#74hh (num-list on))))))))
                

(define (p#74 on count)
  (p#74h on)
  (if (= on 1000001)
      count
      (if (= (hash-ref !loops on) 60)
          (p#74 (+ on 1) (+ count 1))
          (p#74 (+ on 1) count))))
|#

(define (p#75 vec on col max)
  (if (= col max)
      vec
      (if (= on max)
          (p#75 vec 1 (+ col 1) max)
          (if (> on col)
              (begin
                (vector-set! vec on (+ (vector-ref vec on) (vector-ref vec (- on col))))
                (p#75 vec (+ on 1) col max))
              (p#75 vec (+ on 1) col max))
              )))

(define (prime?# n)
  (if (prime? n)
      1
      0))

(define (p#77h vec on col max)
  (if (> (vector-ref vec (- on 1)) 5000)
      (vector-ref vec (- on 1)) 5000)
      (if (= col max)
          vec
          (if (= on max)
              (p#77h vec (next col p) (next col p) max)
              (begin
                (vector-set! vec on (+ (vector-ref vec on) (vector-ref vec (- on col))))
                (p#77h vec (+ on 1) col max))
              )))


(define (p#77 vec on max)
  (if (= on max)
      (p#77h vec 3 3 max)
      (begin
        (if (even? on)
            (vector-set! vec on 1)
            (vector-set! vec on 0))
        (p#77 vec (+ on 1) max))))


(define (p#78 vec on col max div)
  (if (= col max)
      vec
      (if (= on max)
          (if (integer? (/ (vector-ref vec col) div))
              (vector col vec)
              (p#78 vec 1 (+ col 1) max div))
          (if (> on col)
              (begin
                (vector-set! vec on (+ (vector-ref vec on) (vector-ref vec (- on col))))
                (p#78 vec (+ on 1) col max div))
              (p#78 vec (+ on 1) col max div))
              )))

(define (p#80sh sqr on accum setter)
  (set! setter (floor sqr))
  (if (= on 21)
      accum
      (p#80sh (* 10 (- sqr setter)) (+ on 1) (+ accum setter) 0)))

(define (p#80s n)
  (if (integer? (sqrt n))
      0
      (p#80sh (sqrt n) 1 0 0)))

(define 80x80 (vector
               4445 ))

(define (p#81s row column)
  (vector-ref 80x80 (- (+ column (* (- row 1) 80)) 1)))

(define (p#81s2 row column)
  (if
   (and (< column 81) (< row 81))
   (hash-ref value (+ column (* (- row 1) 80)))
   100000000000000000))

(define value (make-hash))

(define (p#81h row column)
  (if (or (> column 80) (> row 80))
      0
      (if (= row column 80)
          (p#81s 80 80)
          (if (hash-has-key? value (+ column (* (- row 1) 80)))
              (p#81s row column)
              (begin
                (p#81h (+ row 1) column)
                (p#81h row (+ column 1))
                (hash-set! value (+ column (* (- row 1) 80))
                           (+ (p#81s row column)
                              (min
                               (p#81s2 (+ row 1) column)
                               (p#81s2 row (+ column 1))))))))))

(define (p#82s row column)
  (vector-ref 80x80 (- (+ column (* (- row 1) 80)) 1)))

(define (p#82s2h row column nrow accum)
  (if (= row nrow)
      (begin
        (p#82h row (+ column 1))
        (+ (p#82s row column) accum (p#81s2 row (+ column 1))))
      (if (> row nrow)
          (p#82s2h (- row 1) column nrow (+ (p#82s row column) accum))
          (p#82s2h (+ row 1) column nrow (+ (p#82s row column) accum)))))

(define (p#82s2 row column nrow)
  (p#82s2h row column nrow 0))

(define (p#82sah row column on small)
  (if (= on 81)
      small
      (p#82sah row column (+ on 1) (min (p#82s2 row column on) small))))

(define (p#82sa row column)
  (p#82sah row column 1 10000000000))

(define (p#82s2a on small)
  (if (= on 81)
      small
      (p#82s2a (+ on 1) (min (p#82sa on 1) small))))

(define (p#82)
  (p#82s2a 1 1000000000000))

(define (p#82h row column)
  (if (= column 80)
      (hash-set! value (+ column (* (- row 1) 80)) (p#82s row column))
      (if (hash-has-key? value (+ column (* (- row 1) 80)))
          (p#81s2 row column)
          (hash-set! value (+ column (* (- row 1) 80))
                     (+
;;                      (p#82s row column)
                        (p#82sa row column))))))


(define (p#85s l w)
  (* (triangle l) (triangle w)))

(define (p#85h onl onw close)
  (if (> (p#85s onl onw) 2000000)
      (if (= onl 3000)
          close
          (p#85h (+ onl 1) 1 (cons (list (abs (- 2000000 (p#85s onl onw))) onl onw)
                                   (cons (list (abs (- 2000000 (p#85s onl (- onw 1)))) onl onw)
                                         close))))
          (p#85h onl (+ onw 1) close)))

(define (p#85 close l)
  (if (empty? l)
      close
      (if (< (caar l) (car close))
          (p#85 (car l) (cdr l))
          (p#85 close (cdr l)))))

(define (p#86sh n l w h)
  (+
   (sqrt (+ (expt l 2) (expt n 2)))
   (sqrt (+ (expt w 2) (expt (- h n) 2)))))

(define (p#86s l w h)
  (p#86sh (/ (* l h) (+ l w)) l w h))

(define (p#86s? l w h)
  (if (integer? (p#86s l w h))
      1
      0))

(define (p#86h l w h accum max ha)
  (if (> l max)
      (list accum ha)
      (if (> w max)
          (p#86h (+ l 1) (+ l 1) (+ l 1) accum max ha)
          (if (> h max)
              (p#86h l (+ w 1) (+ w 1) accum max ha)
              (if (integer? (p#86s l w h))
                  (p#86h l w (+ h 1) (+ accum (p#86s? l w h)) max (hash-set ha (list l w h) (p#86s l w h)))
                  (p#86h l w (+ h 1) (+ accum (p#86s? l w h)) max ha))))))

(define (p#86 max)
  (p#86h 1 1 1 0 max (make-immutable-hash)))

;; 2 5 7 10 11 13 14 17 19 22 23 25
;; 3 4 6 8 9 12 15 16 18 20 21 24

(define p#87l1 (siv 7080))
(define p#87l2 (siv 374))
(define p#87l3 (siv 90))

(define (vector-sumh v on len)
  (if (< len on)
      0
      (+
       (vector-ref v on)
       (vector-sumh v (+ on 1) len))))

(define (vector-sum v)
  (vector-sumh v 0 (vector-length v)))

(define (p#87h on1 on2 on3 v)
  (if (> on1 7071)
      (if (> on2 368)
          (if (> on3 84)
              v
              (p#87h 2 2 (next on3 p#87l3) v))
          (p#87h 2 (next on2 p#87l2) on3 v))
      (begin
        (cond
         ((< (+ (expt on1 2) (expt on2 3) (expt on3 4)) 50000000)
         (vector-set! v (+ (expt on1 2) (expt on2 3) (expt on3 4)) 1)))
        (p#87h (next on1 p#87l1) on2 on3 v))))

(define (p#87)
  (vector-sum (p#87h 2 2 2 (make-vector 50000000))))

(define (hhk? h e)
  (hash-has-key? h e))

(define (p#90? h1 h2)
  (and
   (or
    (and
     (hhk? h1 0)
     (hhk? h2 1))
    (and
     (hhk? h2 0)
     (hhk? h1 1)))
   (or
    (and
     (hhk? h1 0)
     (hhk? h2 4))
    (and
     (hhk? h2 0)
     (hhk? h1 4)))
   (or
    (and
     (hhk? h1 0)
     (or (hhk? h2 6) (hhk? h2 9)))
    (and
     (hhk? h2 0)
     (or (hhk? h1 6) (hhk? h1 9))))
   (or
    (and
     (hhk? h1 1)
     (or (hhk? h2 6) (hhk? h2 9)))
    (and
     (hhk? h2 1)
     (or (hhk? h1 6) (hhk? h1 9))))
   (or
    (and
     (hhk? h1 2)
     (hhk? h2 5))
    (and
     (hhk? h2 2)
     (hhk? h1 5)))
   (or
    (and
     (hhk? h1 3)
     (or (hhk? h2 6) (hhk? h2 9)))
    (and
     (hhk? h2 3)
     (or (hhk? h1 6) (hhk? h1 9))))
   (or
    (and
     (hhk? h1 4)
     (or (hhk? h2 6) (hhk? h2 9)))
    (and
     (hhk? h2 4)
     (or (hhk? h1 6) (hhk? h1 9))))
   (or
    (and
     (hhk? h1 8)
     (hhk? h2 1))
    (and
     (hhk? h2 8)
     (hhk? h1 1)))))

(define (die n1 n2 n3 n4 n5 n6)
  (make-hash (list (cons n1 1) (cons n2 1) (cons n3 1) (cons n4 1) (cons n5 1) (cons n6 1))))

(define (next-die on1 on2 on3 on4 on5 on6)
  (if (>= on6 10)
      (if (>= on5 9)
          (if (>= on4 8)
              (if (>= on3 7)
                  (if (>= on2 6)
                      (if (>= on1 5)
                          (list)
                          (list (+ on1 1) (+ on1 2) (+ on1 3) (+ on1 4) (+ on1 5) (+ on1 6)))
                      (list on1 (+ on2 1) (+ on2 2) (+ on2 3) (+ on2 4) (+ on2 5)))
                  (list on1 on2 (+ on3 1) (+ on3 2) (+ on3 3) (+ on3 4)))
              (list on1 on2 on3 (+ on4 1) (+ on4 2) (+ on4 3)))
          (list on1 on2 on3 on4 (+ on5 1) (+ on5 2)))
      (list on1 on2 on3 on4 on5 (+ on6 1))))

(define (p#90hh d1 on1 on2 on3 on4 on5 on6)
  (if (>= on6 10)
      (if (>= on1 5)
          (list)
          (apply p#90hh (cons d1 (next-die on1 on2 on3 on4 on5 on6))))
      (if (p#90? d1 (die on1 on2 on3 on4 on5 on6))
          (cons (list d1 (die on1 on2 on3 on4 on5 on6)) (apply p#90hh (cons d1 (next-die on1 on2 on3 on4 on5 on6))))
          (apply p#90hh (cons d1 (next-die on1 on2 on3 on4 on5 on6))))))

(define (p#90h on1 on2 on3 on4 on5 on6)
  (if (>= on6 10)
      (if (>= on1 5)
          (list)
          (apply p#90h (next-die on1 on2 on3 on4 on5 on6)))
      (append
       (p#90hh (die on1 on2 on3 on4 on5 on6) on1 on2 on3 on4 on5 (+ on6 1))
       (apply p#90h (next-die on1 on2 on3 on4 on5 on6)))))

(define (p#90)
  (p#90h 0 1 2 3 4 5))

(define (p#91? x1 y1 x2 y2)
  (if
   (and
    (not (and (= x1 x2) (= y1 y2)))
     (or
      (= (+ (expt x1 2) (expt y1 2) (expt x2 2) (expt y2 2)) (+ (expt (- x1 x2) 2) (expt (- y1 y2) 2)))
      (= (+ (expt x1 2) (expt y1 2) (expt (- x1 x2) 2) (expt (- y1 y2) 2)) (+ (expt x2 2) (expt y2 2)))
      (= (+ (expt x2 2) (expt y2 2) (expt (- x1 x2) 2) (expt (- y1 y2) 2)) (+ (expt x1 2) (expt y1 2)))))
   (begin
;;     (printf "~s ~n" (list x1 y1 x2 y2))
     true)
   false))

(define (p#91h x1 y1 x2 y2 maxer)
  (if (or (>= y2 maxer) (>= x2 maxer) (>= y1 maxer) (>= x1 maxer))
      (if (or (>= x2 maxer)  (>= y1 maxer) (>= x1 maxer))
          (if (or (>= y1 maxer) (>= x1 maxer))
              (if (>= x1 maxer)
                  0
                  (p#91h (+ x1 1) 0 (+ x1 1) 0 maxer))
              (p#91h x1 (+ y1 1) x1 (+ y1 1) maxer))
          (p#91h x1 y1 (+ x2 1) 0 maxer))
      (if (p#91? x1 y1 x2 y2)
          (+ 1 (p#91h x1 y1 x2 (+ y2 1) maxer))
          (p#91h x1 y1 x2 (+ y2 1) maxer))))
                  

(define (p#91 n)
  (p#91h 0 1 0 2 n))

(define p#92ha (make-hash (list (cons 89 1) (cons 1 0))))
(define p#92v (make-vector 10000001))
(vector-set! p#92v 89 89)

(define (p#92fill on)
  (vector-set! p#92v on (p#92?h on))
  (cond
    ((< on 10000000) (p#92fill (+ on 1)))))

(define (p#92?h n)
  (if (= n 0)
      0
      (+ (expt (remainder n 10) 2) (p#92?h (/ (- n (remainder n 10)) 10)))))
  
(define (p#92? n)
  (if (or (= n 1) (= n 89))
      n
      (begin
        (vector-set! p#92v n (p#92? (vector-ref p#92v n)))
        (vector-ref p#92v n))))

(define (p#92 n max)
  (if (> n max)
      0
      (begin
        (p#92? n)
        (+ -1 (vector-ref p#92v n) (p#92 (+ n 1) max)))))

(define (p#57? num den)
  (> (length (num-list num)) (length (num-list den))))

(define (p#57h on num den lnum lden)
  (if (> on 1000)
      0
      (if (p#57? num den)
          (+ 1 (p#57h (+ on 1) (+ num num lnum) (+ den den lden) num den))
          (p#57h (+ on 1) (+ num num lnum) (+ den den lden) num den))))

(define (p#57)
  (p#57h 1 3 2 1 1))

(define (trues v on)
    (if (= on (vector-length v))
        0
        (if (vector-ref v on)
            (+ 1 (trues v (+ on 1)))
            (trues v (+ on 1)))))

(define (vShrinkh v new on1 on2)
  (if (= on1 (vector-length v))
      new
      (if (vector-ref v on1)
          (begin
            (vector-set! new on2 on1)
            (vShrinkh v new (+ on1 1) (+ on2 1)))
          (vShrinkh v new (+ on1 1) on2))))

(define (vShrink v)
  (vShrinkh v (make-vector (trues v 0) 0) 0 0))
#|
(define pvec (vShrink (siv 3000)))

(define (p#60?p p1 p2)
  (and
   (prime? (list->num (append (num-list p1) (num-list p2))))
   (prime? (list->num (append (num-list p2) (num-list p1))))))

(define (p#60pairshh on1 on2)
  (if (> on2 429)
      (list)
      (if (p#60?p (vector-ref pvec on1) (vector-ref pvec on2))
          (cons
           (vector-ref pvec on2)
           (p#60pairshh on1 (+ on2 1)))
          (p#60pairshh on1 (+ on2 1)))))

(define (p#60pairsh on newH)
  (if (> on 429)
      newH
      (begin
        (hash-set! newH (vector-ref pvec on) (p#60pairshh on on))
        (p#60pairsh (+ on 1) newH))))


(define p#60pairs (p#60pairsh 0 (make-hash))) ;;deletable runner

(define (searchh start onP onN l amount)
  (if (empty? l)
      1000000000
      (min
       (search start (car l) (+ onN 1) amount)
       (searchh start onP onN (cdr l)))))

(define (search start onP onN amount)
  (if (= onN amount)
      (if (p#60?p onP start)
          onP
          1000000000)
      (+ onP (searchh start onP onN (hash-ref p#60pairs onP) amount))))|#

(define (logB base num)
  (/ (log num) (log base)))

(define (toB10h l b)
  (if (empty? l)
      0
      (+ (car l) (* b (toB10h (cdr l) b)))))

(define (toB10 num base)
  (toB10h (reverse (num-list num)) base))

(define (digits num base)
  (if (> base num)
      1
      (+ 1 (digits (/ num base) base))))

(define (baseCh num nBase digit)
  (if (= digit 0)
      (list)
      (cons
       (floor (/ num (expt nBase (- digit 1))))
       (baseCh (- num (* (expt nBase (- digit 1)) (floor (/ num (expt nBase (- digit 1)))))) nBase (- digit 1)))))

(define (baseC num base nBase)
  (if (= num 0)
      0
      (list->num (baseCh (toB10 num base) nBase (digits (toB10 num base) nBase)))))

(define (xorIh l1 l2)
  (if (and (empty? l1) (empty? l2))
      (list)
      (if (or (empty? l1) (empty? l2))
          (append l2 l1)
          (cons
           (modulo (+ (car l1) (car l2)) 2)
           (xorIh (cdr l1) (cdr l2))))))
           

(define (xorI n1 n2)
  (toB10 (list->num (reverse (xorIh (reverse (num-list (baseC n1 10 2))) (reverse (num-list (baseC n2 10 2)))))) 2))

(define xorN (list 79 59 12 2 79 35 8 28 20 2 3 68 8 9 68 45 0 12 9 67 68 4 7 5 23 27 1 21 79 85 78 79 85 71 38
                  10 71 27 12 2 79 6 2 8 13 9 1 13 9 8 68 19 7 1 71 56 11 21 11 68 6 3 22 2 14 0 30 79 1 31 6
                  23 19 10 0 73 79 44 2 79 19 6 28 68 16 6 16 15 79 35 8 11 72 71 14 10 3 79 12 2 79 19 6 28 68
                  32 0 0 73 79 86 71 39 1 71 24 5 20 79 13 9 79 16 15 10 68 5 10 3 14 1 10 14 1 3 71 24 13 19 7
                  68 32 0 0 73 79 87 71 39 1 71 12 22 2 14 16 2 11 68 2 25 1 21 22 16 15 6 10 0 79 16 15 10 22
                  2 79 13 20 65 68 41 0 16 15 6 10 0 79 1 31 6 23 19 28 68 19 7 5 19 79 12 2 79 0 14 11 10 64
                  27 68 10 14 15 2 65 68 83 79 40 14 9 1 71 6 16 20 10 8 1 79 19 6 28 68 14 1 68 15 6 9 75 79 5
                  9 11 68 19 7 13 20 79 8 14 9 1 71 8 13 17 10 23 71 3 13 0 7 16 71 27 11 71 10 18 2 29 29 8 1
                  1 73 79 81 71 59 12 2 79 8 14 8 12 19 79 23 15 6 10 2 28 68 19 7 22 8 26 3 15 79 16 15 10 68
                  3 14 22 12 1 1 20 28 72 71 14 10 3 79 16 15 10 68 3 14 22 12 1 1 20 28 68 4 14 10 71 1 1 17 10
                  22 71 10 28 19 6 10 0 26 13 20 7 68 14 27 74 71 89 68 32 0 0 71 28 1 9 27 68 45 0 12 9 79 16
                  15 10 68 37 14 20 19 6 23 19 79 83 71 27 11 71 27 1 11 3 68 2 25 1 21 22 11 9 10 68 6 13 11 18
                  27 68 19 7 1 71 3 13 0 7 16 71 28 11 71 27 12 6 27 68 2 25 1 21 22 11 9 10 68 10 6 3 15 27 68
                  5 10 8 14 10 18 2 79 6 2 12 5 18 28 1 71 0 2 71 7 13 20 79 16 2 28 16 14 2 11 9 22 74 71 87 68
                  45 0 12 9 79 12 14 2 23 2 3 2 71 24 5 20 79 10 8 27 68 19 7 1 71 3 13 0 7 16 92 79 12 2 79 19
                  6 28 68 8 1 8 30 79 5 71 24 13 19 1 1 20 28 68 19 0 68 19 7 1 71 3 13 0 7 16 73 79 93 71 59 12
                  2 79 11 9 10 68 16 7 11 71 6 23 71 27 12 2 79 16 21 26 1 71 3 13 0 7 16 75 79 19 15 0 68 0 6 18
                  2 28 68 11 6 3 15 27 68 19 0 68 2 25 1 21 22 11 9 10 72 71 24 5 20 79 3 8 6 10 0 79 16 8 79 7
                  8 2 1 71 6 10 19 0 68 19 7 1 71 24 11 21 3 0 73 79 85 87 79 38 18 27 68 6 3 16 15 0 17 0 7 68
                  19 7 1 71 24 11 21 3 0 71 24 5 20 79 9 6 11 1 71 27 12 21 0 17 0 7 68 15 6 9 75 79 16 15 10 68
                  16 0 22 11 11 68 3 6 0 9 72 16 71 29 1 4 0 3 9 6 30 2 79 12 14 2 68 16 7 1 9 79 12 2 79 7 6 2
                  1 73 79 85 86 79 33 17 10 10 71 6 10 71 7 13 20 79 11 16 1 68 11 14 10 3 79 5 9 11 68 6 2 11 9
                  8 68 15 6 23 71 0 19 9 79 20 2 0 20 11 10 72 71 7 1 71 24 5 20 79 10 8 27 68 6 12 7 2 31 16 2
                  11 74 71 94 86 71 45 17 19 79 16 8 79 5 11 3 68 16 7 11 71 13 1 11 6 1 17 10 0 71 7 13 10 79 5
                  9 11 68 6 12 7 2 31 16 2 11 68 15 6 9 75 79 12 2 79 3 6 25 1 71 27 12 2 79 22 14 8 12 19 79 16
                  8 79 6 2 12 11 10 10 68 4 7 13 11 11 22 2 1 68 8 9 68 32 0 0 73 79 85 84 79 48 15 10 29 71 14
                  22 2 79 22 2 13 11 21 1 69 71 59 12 14 28 68 14 28 68 9 0 16 71 14 68 23 7 29 20 6 7 6 3 68 5
                  6 22 19 7 68 21 10 23 18 3 16 14 1 3 71 9 22 8 2 68 15 26 9 6 1 68 23 14 23 20 6 11 9 79 11 21
                  79 20 11 14 10 75 79 16 15 6 23 71 29 1 5 6 22 19 7 68 4 0 9 2 28 68 1 29 11 10 79 35 8 11 74
                  86 91 68 52 0 68 19 7 1 71 56 11 21 11 68 5 10 7 6 2 1 71 7 17 10 14 10 71 14 10 3 79 8 14 25
                  1 3 79 12 2 29 1 71 0 10 71 10 5 21 27 12 71 14 9 8 1 3 71 26 23 73 79 44 2 79 19 6 28 68 1
                  26 8 11 79 11 1 79 17 9 9 5 14 3 13 9 8 68 11 0 18 2 79 5 9 11 68 1 14 13 19 7 2 18 3 10 2 28
                  23 73 79 37 9 11 68 16 10 68 15 14 18 2 79 23 2 10 10 71 7 13 20 79 3 11 0 22 30 67 68 19 7 1
                  71 8 8 8 29 29 71 0 2 71 27 12 2 79 11 9 3 29 71 60 11 9 79 11 1 79 16 15 10 68 33 14 16 15 10
                  22 73))

(define p#61min 97)
(define p#61max 122)

(define (xorCipher l code on)
  (if (empty? l)
      ""
      (string-append
       (string (integer->char (xorI (car l) (nth (+ on 1) code))))
       (xorCipher (cdr l) code (modulo (+ on 1) (length code))))))

(define (xorCipherSmart l code on)
  (define myChar (xorI (car l) (nth (+ on 1) code)))
  (if (empty? l)
      ""
      (if (p#61h myChar)
          (string-append
           (string (integer->char myChar))
           (xorCipherSmart (cdr l) code (modulo (+ on 1) (length code))))
          "fail")))

(define (p#61h int)
  (or
   (and
    (< int 123)
    (> int 50))))
   

(define (p#61 n1 n2 n3)
  (define cipher "")
  (if (> n1 p#61max)
      (printf "done")
      (if (> n2 p#61max)
          (p#61 (+ n1 1) p#61min p#61min)
          (if (> n3 p#61max)
              (p#61 n1 (+ n2 1) p#61min)
              (begin
                (set! cipher (xorCipherSmart xorN (list n1 n2 n3) 0))
                (if (equal? "fail" cipher)
                    (p#61 n1 n2 (+ n3 1))
                    (begin
                      (printf "the code is ~s ~s ~s and the messega is: ~n ~n ~a" n1 n2 n3 cipher)
                      (p#61 n1 n2 (+ n3 1)))))))))

(define (smallFloorh n on)
  (if (> on n)
      (- on 1)
      (smallFloorh n (+ on 1))))

(define (smallFloor n)
  (smallFloorh n 0))

(define (rFractionh n ha)
  (define floo (smallFloor n))
  (if (hash-has-key? ha (floor (* 1000 n)))
      (list)
      (cons floo (rFractionh (/ 1 (- n floo)) (hash-set ha (floor (* 1000 n)) floo)))))

(define (rFraction n)
  ;(list
   ;(smallFloor n)
   (rFractionh (/ 1 (- n (smallFloor n))) (make-immutable-hash)))
;)

(define (rFraction2h sq num n ha)
  (define floo (smallFloor (* num (/ (- (sqrt sq) n) (- sq (* n n))))))
  ;(printf "We are at ~s/(~s+~s). ~n" num sq n)
  (if (hash-has-key? ha (list num n))
      (list)
      (cons
       floo
       (rFraction2h sq (/ (- sq (* n n)) num)
                    (- (- 0 n) (* floo (/ (- sq (* n n)) num)))
                    (hash-set ha (list num n) floo)))))

(define (rFraction2 sq)
  (rFraction2h sq 1 (- 0 (smallFloor (sqrt sq))) (make-immutable-hash)))

(define (p#64 on)
  (if (> on 10000)
      0
      (if (and
           (not (square-number? on))
           (odd? (length (rFraction2 on))))
          (begin
            ;(printf "~s: ~s~n~n" on (rFraction (sqrt on)))
            (+ 1 (p#64 (+ on 1))))
            (p#64 (+ on 1)))))

(define (add-frac f1 f2)
  (define n1 (car f1))
  (define n2 (car f2))
  (define d1 (cdr f1))
  (define d2 (cdr f2))
  (define lc (lcm d1 d2))
  (cons
   (+ (* n1 (/ lc d1)) (* n2 (/ lc d2)))
   (lcm d1 d2)))

(define (revP p)
  (cons (cdr p) (car p)))

(define (p#65 on end)
  (if (and (= on 0) (= on end))
      (cons 2 1)
      (if (= on 0)
          (add-frac
           (cons 2 1)
           (revP (p#65 (+ on 1) end)))
          (if (= on end)
              (if (= (modulo on 3) 2)
                  (cons (* 2 (+ 1 (quotient on 3))) 1)
                  (cons 1 1))
              (if (= (modulo on 3) 2)
                  (add-frac
                   (cons (* 2 (+ 1 (quotient on 3))) 1)
                   (revP (p#65 (+ on 1) end)))
                  (add-frac
                   (cons 1 1)
                   (revP (p#65 (+ on 1) end))))))))

(define (sqrtLh n max min)
  (define av (quotient (+ max min) 2))
  (if (<= (- max min) 1)
      min
      (if (> (expt av 2) n)
          (sqrtLh n av min)
          (sqrtLh n max av))))

(define (sqrtL n len)
  (sqrtLh (* n (expt 10 (* 2 (- len 1)))) (* n (expt 10 (* 2 (- len 1)))) 0))

(define (p#80 on)
  (if (> on 100)
      0
      (if (square-number? on)
          (p#80 (+ on 1))
          (+
           (sum (num-list (sqrtL on 100)))
           (p#80 (+ on 1))))))

(define (only l func)
  (if (empty? l)
      l
      (if (func (car l))
          (cons (car l) (only (cdr l) func))
          (only (cdr l) func))))

(define (quick-sort l)
  (if (or (empty? l) (empty? (cdr l)))
      l
      (append
       (quick-sort (only (cdr l) (lambda (x) (<= x (car l)))))
       (cons
        (car l)
        (quick-sort (only (cdr l) (lambda (x) (> x (car l)))))))))

(define (quick-sort2 l)
  (if (or (empty? l) (empty? (cdr l)))
      l
      (append
       (quick-sort2 (only l (lambda (x) (< x (car l)))))
       (cons
        (car l)
        (quick-sort2 (only l (lambda (x) (> x (car l)))))))))
         
(define (p#93s ln lo)
  (if (empty? lo)
      (car ln)
      (cond
        ((= (car lo) 1) (+ (car ln) (p#93s (cdr ln) (cdr lo))))
        ((= (car lo) 2) (- (car ln) (p#93s (cdr ln) (cdr lo))))
        ((= (car lo) 3) (* (car ln) (p#93s (cdr ln) (cdr lo))))
        ((= (car lo) 4) (* (car ln) (p#93s (cdr ln) (cdr lo))))
        ((= (car lo) 5) (+ (- 0 (car ln)) (p#93s (cdr ln) (cdr lo))))
        ((= (car lo) 6) (* (/ 1 (car ln)) (p#93s (cdr ln) (cdr lo)))))))

(define (longestchain l on)
  (if (empty? l)
      (- on 1)
      (if (= (car l) on)
          (longestchain (cdr l) (+ on 1))
          (if (= (car l) (- on 1))
              (longestchain (cdr l) on)
              (- on 1)))))

(define (p#93hhh l o1 o2 o3)
  (if (= o1 7)
      (list)
      (if (= o2 7)
          (p#93hhh l (+ o1 1) 1 1)
          (if (= o3 7)
              (p#93hhh l o1 (+ o2 1) 1)
              (cons
               (p#93s l (list o1 o2 o3))
               (p#93hhh l o1 o2 (+ o3 1)))))))

(define (p#93hh l)
  (if (empty? l)
      (list)
      (append
       (p#93hhh (car l) 1 1 1)
       (p#93hh (cdr l)))))
  

(define (p#93h a b c d longest best)
  (define long 0)
  (cond
    ((> a 6) (list best longest))
    ((> b 7) (p#93h (+ a 1) (+ a 2) (+ a 3) (+ a 4) longest best))
    ((> c 8) (p#93h a (+ b 1) (+ b 2) (+ b 3) longest best))
    ((> d 9) (p#93h a b (+ c 1) (+ c 2) longest best))
    (else
     ;;(set! long (longestchain (quick-sort2 (map (lambda (x) (max x (- 0 x))) (p#93hh (permute (list a b c d))))) 1))
     (set! long (longestchain (quick-sort2 (only (p#93hh (permute (list a b c d))) (lambda (x) (and (> x 0) (integer? x))))) 1))
     (if (> long longest)
         (p#93h a b c (+ d 1) long (list a b c d))
         (p#93h a b c (+ d 1) longest best)))))

(define (p#93)
  (p#93h 1 1 1 1 0 (list 1 1 1 1)))

(define (factorer2h num on)
  (if (> (* on on) num)
      (list)
      (if (integer? (/ num on))
          (if (= (* on on) num)
              (cons on (factorer2h num (+ on 1)))
              (cons on (cons (/ num on) (factorer2h num (+ on 1)))))
          (factorer2h num (+ on 1)))))

(define (factorer2 num)
  (factorer2h num 1))

(define p#95nums (make-hash (list (cons 0 (cons 2 0)))))

(define (p#95n on)
  (- (sum (factorer2 on)) on))

(define (p#95h start on amount mini)
  (if (or (prime? on) (> on 1000000))
      (begin
        (hash-set! p#95nums start (cons 1 1))
        (cons 1 1))
      (if (and (hash-has-key? p#95nums on) (not (equal? (hash-ref p#95nums on) "n/a")))
          (if (equal? (hash-ref p#95nums on) "waiting")
              "n/a"
              (begin
                (hash-set! p#95nums start (hash-ref p#95nums on))
                (hash-ref p#95nums on)))
          (if (= start on)
              (begin
                (hash-set! p#95nums start (cons amount mini))
                (cons amount mini))
              (begin
                (hash-set! p#95nums on "waiting")
                (hash-set! p#95nums on (p#95h start (p#95n on) (+ amount 1) (min mini on)))
                (hash-ref p#95nums on))))))

(define (p#95h2 start on amount mini)
  (if (or (prime? on) (> on 1000000))
      (hash-set! p#95nums start (cons 1 1))
      (if (hash-has-key? p#95nums on)
          (hash-set! p#95nums start (hash-ref p#95nums on))
          (if (= start on)
              (hash-set! p#95nums start (cons amount mini))
              (p#95h2 start (p#95n on) (+ amount 1) (min mini on))))))

(define (p#95fill on max)
  (cond
    ((< on max)
     (begin
       (if (prime? on)
           (hash-set! p#95nums on (cons 1 1))
           (begin
             (p#95h on (p#95n on) 1 on)
             (cond
               ((not (hash-has-key? p#95nums on)) (hash-set! p#95nums on (cons 1 1))))))
       (p#95fill (+ on 1) max)))))

(define (p#95fill2 on max)
  (cond
    ((< on max)
     (begin
       (if (prime? on)
           (hash-set! p#95nums on (cons 1 1))
           (p#95h2 on (p#95n on) 1 on))
       (p#95fill2 (+ on 1) max)))))

(define (p#95-h on largest final)
  (if (= on 1000000)
      final
      (if (and
           (not (string? (hash-ref p#95nums on)))
           (> (car (hash-ref p#95nums on)) largest))
          (p#95-h (+ on 1) (car (hash-ref p#95nums on)) (cdr (hash-ref p#95nums on)))
          (p#95-h (+ on 1) largest final))))

(define (p#95)
  (p#95fill 1 1000000)
  (p#95-h 1 1 1))

(define p#67v (list->vector (list 59)))
(define p#67ha (make-hash))

(define (p#67hh row col)
  (vector-ref p#67v (+ (* row (- row 1) 1/2) col -1)))

(define (p#67er row col)
  (if (= row 101)
      (begin
        (hash-set! p#67ha (cons row col) 0)
        0)
      (if (hash-has-key? p#67ha (cons row col))
          (hash-ref p#67ha (cons row col))
          (begin
            (p#67er (+ row 1) (+ col 1))
            (p#67er (+ row 1) col)
            (hash-set! p#67ha (cons row col) (+ (p#67hh row col) (max (hash-ref p#67ha (cons (+ row 1) (+ col 1)))
                                                                     (hash-ref p#67ha (cons (+ row 1) col)))))
            (hash-ref p#67ha (cons row col))))))

(define sq2 (sqrt 1/2))
(define (p#100? n)
  (define num (inexact->exact (ceiling (* sq2 n))))
  (define frac (cons (* 2 num (- num 1)) (* n (- n 1))))
  (if (= (car frac) (cdr frac))
      0
      (if (> (car frac) (cdr frac))
          1
          -1)))

(define (p#100 on)
  (define 100er (p#100? on))
  (if (= 100er 0)
      (list (ceiling (* sq2 on)) on)
      (p#100 (+ on 1))))

(define (p#100b onN onD)
  (if (< onN (* onD sq2))
      (p#100b (+ onN 1) onD)
      (if (= (* 2 onN (- onN 1)) (* onD (- onD 1)))
          (cons onN onD)
          (p#100b onN (+ onD 1)))))

(define (p#100th start finish last1 last2)
  (if (> start finish)
      (begin
        (printf "done")
        (list))
      (begin
        (cond
          ((= 0 (p#100? start)) (begin
                                  (printf "~s | ~s~n" (ceiling (* sq2 start)) start)
                                  (cons
                                   start
                                   (p#100th (+ (inexact->exact (floor (* start (/ last1 last2)))) 1)
                                            finish start last1))))
          (else (p#100th (+ start 1) finish last1 last2))))))

(define (p#100t start finish)
  (p#100th start finish 4 1))

(define (allR l)
    (if (empty? (cdr l))
        (list)
        (cons
         (/ (* 1.0 (car l)) (cadr l))
         (allR (cdr l)))))

(define (p#101f n)
    (-
     (+
      (expt n 0)
      (expt n 2)
      (expt n 4)
      (expt n 6)
      (expt n 8)
      (expt n 10))
     (+
      (expt n 1)
      (expt n 3)
      (expt n 5)
      (expt n 7)
      (expt n 9))))

(define (dif l)
  (if (empty? (cdr l))
      (list)
      (cons (- (car l) (cadr l)) (dif (cdr l)))))

(define (nthDif l n)
  (if (= n 1)
      (car l)
      (nthDif (dif l) (- n 1))))

(define (p#101s l k)
  (if (= k 0)
      (car l)
      (+ (car l) (p#101s (dif l) (- k 1)))))

(define (p#101gh f on amount)
  (if (= on amount)
      (list)
      (cons (f on) (p#101gh f (+ on 1) amount))))

(define (p#101g f amount)
  (p#101gh f 1 amount))

(define (p#101h l on end)
  (if (= on end)
      0
      (+ (p#101s (reverse (front on l)) (- on 1)) (p#101h l (+ on 1) end))))

(define (p#101 f end)
  (p#101h (p#101g f end) 1 end))

(define (noEmpty l)
  (if (empty? l)
      l
      (if (empty? (car l))
          (noEmpty (cdr l))
          (cons (car l) (noEmpty (cdr l))))))

(define (allSetsh e sets)
  (if (empty? sets)
      (list)
      (cons (list (cons e (caar sets)) (cadar sets))
            (cons (list (caar sets) (cons e (cadar sets)))
                  (cons (car sets)
                        (allSetsh e (cdr sets)))))))

(define (allSets l)
  (if (empty? (cdr l))
      (list (list (list (car l)) (list))
            (list (list) (list (car l)))
            (list (list) (list)))
      (allSetsh (car l) (allSets (cdr l)))))

(define (p#103setsh sets)
  (if (empty? sets)
      sets
      (if (or (equal? (caar sets) (list)) (equal? (cadar sets) (list)))
          (p#103setsh (cdr sets))
          (cons (car sets)
                (p#103setsh (cdr sets))))))

(define (p#103sets l)
  (p#103setsh (allSets l)))

(define (biggestSum l)
  (if (empty? l)
      0
      (max (sum (car l)) (biggestSum (cdr l)))))

(define (noEqual l e)
  (if (empty? l)
      true
      (if (= (car l) e)
          false
          (noEqual (cdr l) e))))

(define (p#103?h l)
  (define len1 0)
  (define len2 0)
  (if (empty? l)
      true
      (begin
        (set! len1 (length (caar l)))
        (set! len2 (length (cadar l)))
        (if (> len2 len1)
            (p#103?h (cdr l))
            (if (= len1 len2)
                (if (= (sum (caar l)) (sum (cadar l)))
                    false
                    (p#103?h (cdr l)))
                (if (> (sum (caar l)) (sum (cadar l)))
                    (p#103?h (cdr l))
                    false))))))

(define (p#103? l)
  (p#103?h (p#103sets l)))

(define p#103ha (make-hash))

(define (>> a b)
  (> a (+ b 1)))
(define toHigh 55)
(define (p#103allNext on1 on2 on3 on4 on5 on6 on7)
  (define end (list))
  (cond ((>> on2 on1) (set! end (cons (p#103h (+ 1 on1) on2 on3 on4 on5 on6 on7) end))))
  (cond ((>> on3 on2)  (set! end (cons (p#103h on1 (+ 1 on2) on3 on4 on5 on6 on7) end))))
  (cond ((>> on4 on3) (set! end (cons (p#103h on1 on2 (+ 1 on3) on4 on5 on6 on7) end))))
  (cond ((>> on5 on4) (set! end (cons (p#103h on1 on2 on3 (+ 1 on4) on5 on6 on7) end))))
  (cond ((>> on6 on5) (set! end (cons (p#103h on1 on2 on3 on4 (+ 1 on5) on6 on7) end))))
  (cond ((>> on7 on6) (set! end (cons (p#103h on1 on2 on3 on4 on5 (+ 1 on6) on7) end))))
  (set! end (cons (p#103h on1 on2 on3 on4 on5 on6 (+ 1 on7)) end))
  end)

(define (p#103hhh l best bestV)
  (if (empty? l)
      best
      (if (< (cdar l) bestV)
          (p#103hhh (cdr l) (car l) (cdar l))
          (p#103hhh (cdr l) best bestV))))

(define (p#103hh l)
  (p#103hhh (cdr l) (car l) (cdar l)))

(define best 500)
(define (p#103h on1 on2 on3 on4 on5 on6 on7)
  (define l (list on1 on2 on3 on4 on5 on6 on7))
  (define s (+ on1 on2 on3 on4 on5 on6 on7))
  (define b 0)
  (cond
    ((hash-has-key? p#103ha l) (hash-ref p#103ha l))
    ((>= s best)
      (begin
        (hash-set! p#103ha l (cons l 999999))
        (cons l 999999)))
    ((p#103? (list on1 on2 on3 on4 on5 on6 on7))
     (begin
       (set! best s)
       (hash-set! p#103ha l (cons l s))
       (cons l s)))
    (else
     (begin
       (set! b (p#103hh (p#103allNext on1 on2 on3 on4 on5 on6 on7)))
       (hash-set! p#103ha l b)
       b))))

(define (10in n)
  (if (< n 10)
      0
      (+ 1 (10in (/ n 10)))))

(define (p#104?a n)
   (equal? (sort (num-list (modulo n 1000000000)) <) (list 1 2 3 4 5 6 7 8 9)))

(define (p#104?b n)
  (equal? (sort (num-list (quotient n (expt 10 (- (10in n) 8)))) <) (list 1 2 3 4 5 6 7 8 9)))

(define (p#104? n)
  (and (p#104?a n) (p#104?b n)))

(define (p#104s n)
  (modulo n 1000000000))

(define fibon (cons (cons 1 1) (cons 0 0)))
(define (p#104h on1 on2 on#)
  (define ourfib 0)
  (if (p#104?a on1)
      (begin
        (set! ourfib (fibh (- on# (caar fibon)) (cdar fibon) (cddr fibon)))
        (if (p#104?b ourfib)
            (begin
              (printf "Full at ~s~n" on1)
              on#)
            (begin
              (set! fibon (cons
                           (cons on# ourfib)
                           (car fibon)))
              (printf "One at ~s:~s. It is ~s larger than last~n" on1 on# (- (* 1.0 (caar fibon)) (cadr fibon)))
              (p#104h (p#104s (+ on1 on2)) on1 (+ on# 1)))))
      (p#104h (p#104s (+ on1 on2)) on1 (+ on# 1))))

(define (p#104)
  (p#104h 1 0 1))

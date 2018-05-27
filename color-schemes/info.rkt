#lang info
(define collection "color-schemes")
(define deps '("base"
               "rackunit-lib"))
(define build-deps '("scribble-lib" "racket-doc"))
(define scribblings '(("scribblings/color-schemes.scrbl" ())))
(define pkg-desc "Description Here")
(define version "0.0")
(define pkg-authors '(goobjar))

(define framework:color-schemes
  '(#hash((colors
           .
           ((framework:syntax-color:scheme:string
             #(211 72 255))
            (framework:syntax-color:scheme:constant
             #(211 72 255))
            (framework:syntax-color:scheme:comment
             #(194 158 31))
            (framework:syntax-color:scheme:parenthesis
             #(100 220 120))))
          (name . "Modern"))))
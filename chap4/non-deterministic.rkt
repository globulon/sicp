(define (require p)
  (if (not p) (amb)))


(define (an-element-of items)
  (require (not (null?) item))
  (amb (car items) (an-element-of items)))

(define (an-integer-starting-from n)
  (amb n (an-integer-starting-from (+ n 1))))

(define (square n)
  (* n n))

(define (an-integer-between low high)
  (require (<= low high))
  (amb low (an-integer-between (+ low 1) high)))
 
(define (a-pythagorean-triple-between low high)
  (let ((i (an-integer-between low high)))
    (let ((j (an-integer-between i high)))
      (let ((k (an-integer-between j high)))
        (require (= (square k) (+ (square i) (square j))))
        (list i j k)))))


(define (a-pythagorean-triple-from low)
  (let ((k (an-integer-starting-from low)))
    (let ((i (an-integer-between low k)))
      (let ((j (an-integer-between i k)))
        (require (= (square k) (+ (square i) (square j))))
        (list i j k)))))

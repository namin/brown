((lambda (setter)
   (setter set! setter))
 (make-reifier
  (lambda (e r k)
    (meaning (car (cdr e)) r
      (lambda (v)
        (k (set-cell! (r (car e)) v)))))))

(set! if
  (make-reifier
   (lambda (e r k)
     (meaning (car e) r
       (lambda (v)
         (meaning
             (ef v
                 (car (cdr e))
                 (car (cdr (cdr e))))
           r k))))))

(set! quote
  (make-reifier
   (lambda (e r k) (k (car e)))))

(set! jump
  (make-reifier
   (lambda (e r k) (car e))))

(set! exit
  (lambda (x)
    ((make-reifier
       (lambda (e r k) x)))))

(set! openloop
  (lambda (prompt)
    ((readloop prompt) 'starting-up)))

(set! call/cc
  (lambda (f)
    ((make-reifier
      (lambda (e r k) (k (f k)))))))

(set! new-call/cc
  (lambda (f)
    ((make-reifier
      (lambda (e r k) (f k))))))
